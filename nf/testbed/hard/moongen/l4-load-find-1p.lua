local mg     = require "moongen"
local memory = require "memory"
local device = require "device"
local stats  = require "stats"
local timer  = require "timer"


local BATCH_SIZE = 64 -- packets
local RATE_MIN = 0 -- Mbps
local RATE_MAX = 10000 -- Mbps

local HEATUP_DURATION = 5 -- seconds
local HEATUP_RATE = 20 -- Mbps

local SRC_ETH	= "00:00:00:00:00:00"
local DST_ETH	= "00:00:00:00:00:FF"
local SRC_IP	= "10.0.0.0"
local DST_IP	= "10.0.0.255"
local SRC_PORT	= 0


function configure(parser)
	parser:description("Generates UDP traffic and measure latencies. Edit the source to modify constants like IPs.")
	parser:argument("txDev", "Device to transmit from."):convert(tonumber)
	parser:argument("rxDev", "Device to receive from."):convert(tonumber)
	parser:option("-r --rate", "Transmit rate in Mbit/s."):convert(tonumber)
	parser:option("-p --packetsize", "Packet size."):convert(tonumber)
	parser:option("-s --steps", "Binary search steps."):convert(tonumber)
	parser:option("-d --duration", "Step duration."):convert(tonumber)
end


function runTask(txQueue, rxQueue, packetSize, flowCount, duration)
	local mempool = memory.createMemPool(function(buf)
		buf:getUdpPacket():fill{
			ethSrc = SRC_ETH,
			ethDst = DST_ETH,
			ip4Src = SRC_IP,
			ip4Dst = DST_IP,
			udpSrc = SRC_PORT,
			pktLength = packetSize
		}
	end)

	-- "nil" == no output
	local txCounter = stats:newDevTxCounter(txQueue, "nil")
	local rxCounter = stats:newDevRxCounter(rxQueue, "nil")
	local bufs = mempool:bufArray(BATCH_SIZE)
	local sendTimer = timer:new(duration)

	local dstPort = 0
	while sendTimer:running() and mg.running() do
		bufs:alloc(packetSize)
		for _, buf in ipairs(bufs) do
			local pkt = buf:getUdpPacket()
			pkt.udp.dst = dstPort
			-- incAndWrap does this in a supposedly fast way; in practice it's actually slower!
			-- with incAndWrap this code cannot do 10G line rate
			dstPort = (dstPort + 1) % flowCount
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

function run(name, outFile, txQueue, rxQueue, rate, packetSize, flowCount, duration)
	printf("%s - %d Mbps, %d-byte packets, %d flows, for %d seconds", name, rate, packetSize, flowCount, duration)
	txQueue:setRate(moongenRate(packetSize, rate))
	local task = mg.startTask("runTask", txQueue, rxQueue, packetSize, flowCount, duration)
	local tx, rx = task:wait()
	local loss = (tx - rx) / tx

	printf(" -> %d sent, %d received, %f loss", tx, rx, loss)

	if outFile ~= nil then
		-- Order is important, don't break backwards compatibility
		outFile:write(flowCount .. " " .. rate .. " " .. tx .. " " .. tx/duration .. " " .. loss .. "\n")
	end

	return loss
end


function master(args)
	-- Do not change the name of this file unless you change the rest of the scripts that depend on it!
	local outFile = io.open("mf-find-mg-1p.txt", "w")
	outFile:write("#flows rate #pkt #pkt/s loss\n")

	-- We don't need RX on the txDev or vice-versa, but MoonGen insists rxQueues >= 1 and txQueues >= 1
	local txDev = device.config{port = args.txDev, rxQueues = 1, txQueues = 1}
	local rxDev = device.config{port = args.rxDev, rxQueues = 1, txQueues = 1}
	device.waitForLinks()

	local txQueue = txDev:getTxQueue(0)
	local rxQueue = rxDev:getRxQueue(0)

	for _, flowCount in ipairs({1,10,100,1000,10000,20000,30000,40000,50000,60000,64000,65000,65535}) do
		-- Heatup phase
		local heatupLoss = run("Heatup", nil, txQueue, rxQueue, HEATUP_RATE, args.packetsize, flowCount, HEATUP_DURATION)

		if heatupLoss > 0.001 then
			printf("Heatup caused significant loss; exiting.")
			return	
		end

		local upperBound = RATE_MAX
		local lowerBound = RATE_MIN
		local rate = upperBound

		-- Binary search phase
		for i = 1, (args.steps - 1) do
			local loss = run("Search step " .. i, nil, txQueue, rxQueue, rate, args.packetsize, flowCount, args.duration)
			if (loss < 0.001) then
				-- Minimize pointless iterations
				if rate == upperBound then
					break
				end

				lowerBound = rate
				rate = rate + (upperBound - rate)/2
			else
				upperBound = rate
				rate = lowerBound + (rate - lowerBound)/2
			end
		end

		-- Final phase
		run("Final step", outFile, txQueue, rxQueue, rate, args.packetsize, flowCount, args.duration)
	end
end
