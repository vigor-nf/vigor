local ffi	= require "ffi"
local device	= require "device"
local hist	= require "histogram"
local memory	= require "memory"
local mg	= require "moongen"
local stats	= require "stats"
local timer	= require "timer"
local ts	= require "timestamping"


local BATCH_SIZE = 64 -- packets
local RATE_MIN = 0 -- Mbps
local RATE_MAX = 10000 -- Mbps

local HEATUP_DURATION = 5 -- seconds
local HEATUP_RATE = 20 -- Mbps

local LATENCY_LOAD_RATE = 1000 -- Mbps

local RESULTS_FILE_NAME = 'results.tsv'


-- Arguments for the script
function configure(parser)
	parser:description("Generates UDP traffic and measures throughput.")
	parser:argument("type", "'latency' or 'throughput'.")
	parser:argument("layer", "Layer at which the flows are meaningful."):convert(tonumber)
	parser:argument("txDev", "Device to transmit from."):convert(tonumber)
	parser:argument("rxDev", "Device to receive from."):convert(tonumber)
	parser:option("-p --packetsize", "Packet size."):convert(tonumber)
	parser:option("-d --duration", "Step duration."):convert(tonumber)
	parser:option("-x --reverse", "Number of flows for reverse traffic, if required."):default(0):convert(tonumber)
end

-- Per-layer functions to configure a packet given a counter for the throughput task
local packetThroughputConfigs = {
	[2] = function(pkt, counter)
		-- Override both addresses to make sure the bridge can't use the CPU cache when looking up addresses
		pkt.eth.src:set(counter)
		pkt.eth.dst:set(0xFF0000000000 + counter)
	end,
	[3] = function(pkt, counter)
		pkt.ip4.dst:set(counter)
	end,
	[4] = function(pkt, counter)
		pkt.udp.dst = counter
	end
}
-- Per-layer functions to configure a packet given a counter for the latency task
-- This must result in a non-overlapping packet space with the throughput task, as much as possible!
local packetLatencyConfigs = {
	[2] = function(pkt, counter)
		-- Override both addresses to make sure the bridge can't use the CPU cache when looking up addresses
		pkt.eth.src:set(0xAA0000000000 + counter)
		pkt.eth.dst:set(0xBB0000000000 + counter)
	end,
	[3] = function(pkt, counter)
		pkt.ip4.src:set(counter)
	end,
	[4] = function(pkt, counter)
		pkt.udp.src = counter
	end
}

-- Fills a packet with default values
-- Set the src to the max, so that dst can easily be set to  the counter if needed without overlap
function packetInit(buf, packetSize)
	buf:getUdpPacket():fill{
		ethSrc = "FF:FF:FF:FF:FF:FF",
		ethDst = "00:00:00:00:00:00",
		ip4Src = "255.255.255.255",
		ip4Dst = "0.0.0.0",
		udpSrc = 65535,
		udpDst = 0,
		pktLength = packetSize
	}
end

-- Helper function, has to be global because it's started as a task
function _latencyTask(txQueue, rxQueue, layer, flowCount, duration)
	-- Ensure that the throughput task is running
	mg.sleepMillis(1000)

	local timestamper = ts:newUdpTimestamper(txQueue, rxQueue)
	local hist = hist:new()
	local sendTimer = timer:new(duration - 1) -- we just slept for a second earlier, so deduce that	
	local rateLimiter = timer:new(1 / flowCount) -- ASSUMPTION: The NF is running with 1 second expiry time
	local counter = 0
	
	while sendTimer:running() and mg.running() do
		-- Minimum size for these packets is 84
		local packetSize = 84
		hist:update(timestamper:measureLatency(packetSize, function(buf)
			packetInit(buf, packetSize)
			packetLatencyConfigs[layer](buf:getUdpPacket(), counter)
			-- see throughput for remark about the incAndWrap function
			counter = (counter + 1) % flowCount
		end))
		rateLimiter:wait()
		rateLimiter:reset()
	end
	
	return hist:median(), hist:standardDeviation()
end

-- Starts a latency-measuring task, which returns (median, stdev)
function startMeasureLatency(txQueue, rxQueue, layer, flowCount, duration)
	return mg.startTask("_latencyTask", txQueue, rxQueue, layer, flowCount, duration)
end

-- Helper function, has to be global because it's started as a task
function _throughputTask(txQueue, rxQueue, layer, packetSize, flowCount, duration)
	local mempool = memory.createMemPool(function(buf) packetInit(buf, packetSize) end)
	-- "nil" == no output
	local txCounter = stats:newDevTxCounter(txQueue, "nil")
	local rxCounter = stats:newDevRxCounter(rxQueue, "nil")
	local bufs = mempool:bufArray(BATCH_SIZE)
	local packetConfig = packetThroughputConfigs[layer]
	local sendTimer = timer:new(duration)
	local counter = 0
	
	while sendTimer:running() and mg.running() do
		bufs:alloc(packetSize)
		for _, buf in ipairs(bufs) do
			local pkt = buf:getUdpPacket()
			packetConfig(pkt, counter)
			-- incAndWrap does this in a supposedly fast way; in practice it's actually slower!
			-- with incAndWrap this code cannot do 10G line rate
			counter = (counter + 1) % flowCount
		end

		bufs:offloadIPChecksums() -- UDP checksum is optional, let's do the least possible amount of work
		txQueue:send(bufs)
		txCounter:update()
		rxCounter:update()
	end

	txCounter:finalize()
	rxCounter:finalize()
	return txCounter.total, rxCounter.total
end

-- Starts a throughput-measuring task, which returns (#tx, #rx) packets (where rx == tx iff no loss)
function startMeasureThroughput(txQueue, rxQueue, rate, layer, packetSize, flowCount, duration)
	-- Get the rate that should be given to MoonGen using packets of the given size to achieve the given true rate
	function moongenRate(packetSize, rate)
		-- The rate the user wants is in total Mbits/s
		-- But MoonGen will send it as if the packet size was packetsize+4 (the 4 is for the hardware-offloaded MAC CRC)
		-- when in fact there are 20 bytes of framing on top of that (preamble, start delimiter, interpacket gap)
		-- Thus we must find the "moongen rate" at which MoonGen will transmit at the true rate the user wants
		-- Easiest way to do that is to convert in packets-per-second
		-- Beware, we count packets in bytes and rate in bits so we need to convert!
		-- Also, MoonGen internally calls DPDK in which the rate is an uint16_t, let's avoid floats...
		-- Furthermore, it seems from tests that rates less than 10 are just ignored...
		local byteRate = rate * 1024 * 1024 / 8
		local packetsPerSec = byteRate / (packetSize + 24)
		local moongenByteRate = packetsPerSec * (packetSize + 4)
		local moongenRate = moongenByteRate * 8 / (1024 * 1024)
		if moongenRate < 10 then
			printf("WARNING - Rate %f (corresponding to desired rate %d) too low, will be set to 10 instead.", moongenRate, rate)
			moongenRate = 10
		end
		return math.floor(moongenRate)
	end

	txQueue:setRate(moongenRate(packetSize, rate))
	return mg.startTask("_throughputTask", txQueue, rxQueue, layer, packetSize, flowCount, duration)
end


-- Heats up with packets at the given layer, with the given size and number of flows. Errors if the loss is over 1%.
function heatUp(txQueue, rxQueue, layer, packetSize, flowCount)
		io.write("Heating up for " .. HEATUP_DURATION .. " seconds at " .. HEATUP_RATE .. " Mbps with " .. flowCount .. " flows... ")
		local rx, tx = startMeasureThroughput(txQueue, rxQueue, HEATUP_RATE, layer, packetSize, flowCount, HEATUP_DURATION):wait()
		local loss = (tx - rx) / tx
		if loss > 0.01 then
			io.write("Over 1% loss!\n")
			error("Heatup caused significant loss.")
		end
		
		io.write("OK\n")
end

-- Measure latency under 1G load
function measureLatencyUnderLoad(txDev, rxDev, layer, packetSize, duration, reverseFlowCount)
	-- It's the same filter set every time so not setting it on subsequent attempts is OK
	io.write("!!! IMPORTANT: You can safely ignore the warnings about setting an fdir filter !!!\n")

	-- Do not change the name and format of this file unless you change the rest of the scripts that depend on it!
	local outFile = io.open(RESULTS_FILE_NAME, "w")
	outFile:write("#flows\trate (Mbps)\tmedianLat (ns)\tstdevLat (ns)\n")

	local txThroughputQueue = txDev:getTxQueue(0)
	local rxThroughputQueue = rxDev:getRxQueue(0)
	local txReverseQueue = rxDev:getTxQueue(0) -- yes, the rx/tx inversion is voluntary here
	local rxReverseQueue = txDev:getRxQueue(0)
	local txLatencyQueue = txDev:getTxQueue(1)
	local rxLatencyQueue = rxDev:getRxQueue(1)
	
 	for _, flowCount in ipairs({1,10,100,1000,10000,20000,30000,40000,50000,60000,64000,65000,65535}) do
 		heatUp(txThroughputQueue, rxThroughputQueue, layer, packetSize, flowCount)
 		
 		if reverseFlowCount > 0 then
 			heatUp(txReverseQueue, rxReverseQueue, layer, packetSize, reverseFlowCount)
 		end

		io.write("Measuring latency for " .. flowCount .. " flows... ")
		local throughputTask = startMeasureThroughput(txThroughputQueue, rxThroughputQueue, LATENCY_LOAD_RATE, layer, packetSize, flowCount, duration)
		local latencyTask = startMeasureLatency(txLatencyQueue, rxLatencyQueue, layer, flowCount, duration)

		-- We may have been interrupted
		if not mg.running() then
			io.write("Interrupted\n")
			os.exit(0)
		end			

		local tx, rx = throughputTask:wait()
		local median, stdev = latencyTask:wait()		
		local loss = (tx - rx) / tx
		
		if loss > 0.0001 then
			io.write("Too much loss!\n")
			error("Cannot measure latency when there is too much loss.")
		else
			io.write("median " .. median .. ", stdev " .. stdev .. "\n")
			outFile:write(flowCount .. "\t" .. LATENCY_LOAD_RATE .. "\t" .. median .. "\t" .. stdev .. "\n")
		end
	end
end

-- Measure max throughput with less than 0.1% loss
function measureMaxThroughputWithLowLoss(txDev, rxDev, layer, packetSize, duration, reverseFlowCount)
	-- Do not change the name and format of this file unless you change the rest of the scripts that depend on it!
	local outFile = io.open(RESULTS_FILE_NAME, "w")
	outFile:write("#flows\trate (Mbps)\t#pkts\t#pkts/sec\tloss\n")

	local txQueue = txDev:getTxQueue(0)
	local rxQueue = rxDev:getRxQueue(0)
	local txReverseQueue = rxDev:getTxQueue(0) -- yes, the rx/tx inversion is voluntary here
	local rxReverseQueue = txDev:getRxQueue(0)

 	for _, flowCount in ipairs({1,10,100,1000,10000,20000,30000,40000,50000,60000,64000,65000,65535}) do
 		heatUp(txQueue, rxQueue, layer, packetSize, flowCount)
 		
 		if reverseFlowCount > 0 then
 			heatUp(txReverseQueue, rxReverseQueue, layer, packetSize, reverseFlowCount)
 		end

		io.write("Running binary search with " .. flowCount .. " flows...\n")
		local upperBound = RATE_MAX
		local lowerBound = RATE_MIN
		local rate = upperBound
		-- Binary search phase
		for i = 1, 10 do
			io.write("Step " .. i .. ": " .. rate .. " Mbps... ")
			local rx, tx = startMeasureThroughput(txQueue, rxQueue, rate, layer, packetSize, flowCount, duration):wait()
			
			-- We may have been interrupted
			if not mg.running() then
				io.write("Interrupted\n")
				os.exit(0)
			end
			
			local loss = (tx - rx) / tx
			io.write(tx .. " sent, " .. rx .. " received, loss = " .. loss .. "\n")
			
			-- Stop if the first step is already successful, let's not do pointless iterations
			if (i == 10) or (loss < 0.001 and rate == upperBound) then
				outFile:write(flowCount .. "\t" .. rate .. "\t" .. tx .. "\t" .. tx/duration .. "\t" .. loss .. "\n")
				break
			end
			
			if (loss < 0.001) then				
				lowerBound = rate
				rate = rate + (upperBound - rate)/2
			else
				upperBound = rate
				rate = lowerBound + (rate - lowerBound)/2
			end
		end
	end
end

function master(args)
	-- Max 2 queues for sending (latency + throughput) and 1 queue for receiving (reverse) on TX
	-- Vice-versa for RX
	local txDev = device.config{port = args.txDev, rxQueues = 1, txQueues = 2}
	local rxDev = device.config{port = args.rxDev, rxQueues = 2, txQueues = 1}
	device.waitForLinks()

	measureFunc = nil
	if args.type == 'latency' then
		measureFunc = measureLatencyUnderLoad
	elseif args.type == 'throughput' then
		measureFunc = measureMaxThroughputWithLowLoss
	else
		error("Unknown type.")
	end
	
	measureFunc(txDev, rxDev, args.layer, args.packetsize, args.duration, args.reverse)
end
			-- DST is tricky here, we want to make sure we're fully using the NF parallelization
			-- regardless of the number of cores, so we have to generate packets that first go in the bottom half of ports, then top, then bottom...
			-- and this recursively! the first time it's in the top it should be in the top half of that, the second time in the bottom half, etc.
			-- except this is lua so we can't do easy bit ops (we're running on luaJIT 2.1 beta)
--[[			rem = counter % 8
			if rem == 0 then
				pkt.udp.dst = 1 -- not 0, just in case, but it'll be routed to the same as 0
			elseif rem == 1 then
				pkt.udp.dst = 0x8000
			elseif rem == 2 then
				pkt.udp.dst = 0x4000
			elseif rem == 3 then
				pkt.udp.dst = 0xC000
			elseif rem == 4 then
				pkt.udp.dst = 0x2000
			elseif rem == 5 then
				pkt.udp.dst = 0xA000
			elseif rem == 6 then
				pkt.udp.dst = 0x6000
			elseif rem == 7 then
				pkt.udp.dst = 0xE000
			else
				printf("WTF")
			end
--]]
