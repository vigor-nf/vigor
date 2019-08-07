
local device = require "device"
local moongen = require "moongen"
local memory = require "memory"
local arp    = require "proto.arp"
local stats  = require "stats"
local ts     = require "timestamping"
local filter = require "filter"
local hist   = require "histogram"
local timer  = require "timer"


local NB_TX_QUEUE = 2;
local NB_RX_QUEUE = 2;
--84 is the minimum packet size for timestamping
local PACKET_SIZE = 84;

--jump used to generate pseudo random ip to trigger cache misses in the router
local CACHE_JUMP = 17027;

--enter the nic (port) nummber, the range of routes (between 1 and 2^32) and the delay (to reduce tx load)
function master(nic, nbrRoutes, delay)

	print("Try to configure devices")

	dev = device.config{	--configure device for transmission

		port = nic,
		rxQueues = NB_RX_QUEUE,
		txQueues = NB_TX_QUEUE,	
	}


	device.waitForLinks()	--wait for the devices


	--launch slave task for reception
	moongen.startTask("receivePackets", dev:getRxQueue(0))		
	
	--launch slave task for transmission
	moongen.startTask("sendPackets", dev:getTxQueue(0), nbrRoutes, delay)	

	--launch slave task for packet timestamping
	moongen.startTask("timerSlave", dev:getTxQueue(1), dev:getRxQueue(1), PACKET_SIZE, nbrRoutes)
	
	
	-- wait for child termination
	moongen.waitForTasks() 
	

end


--receive packets and gather stats
function receivePackets(rxQueue)

	local bufs = memory.bufArray()
	local rxCtr = stats:newDevRxCounter(rxQueue.dev)

	while moongen.running() do

		local rx = rxQueue:recv(bufs)

		rxCtr:update()
		bufs:freeAll()
	end
		rxCtr:finalize()

end


--sends packets by iterating on the max number of routes (pseudo random jumps to trigger cache miss)
--you can slow down the load by increasing the delay between packets
function sendPackets(txQueue, nbrRoutes, delay)

 	local txCtr = stats:newDevTxCounter(txQueue, "plain")

	local mem = memory.createMemPool(function(buf)	--fill the packet before to increase performance
		buf:getUdp4Packet():fill{
			pktLength = PACKET_SIZE,
			ethSrc = txQueue, -- device mac
			ethDst = " 90:e2:ba:55:14:39",--rxQueue,
			-- ipDst will be randomized later
			ip4Src = "10.0.0.1",
			udpSrc = 4321,
			udpDst = 1234,
		}

	end)

	local bufs = mem:bufArray()
	
	i = 0

	while moongen.running() do
		bufs:alloc(PACKET_SIZE) --allocate memory for packets
		
		moongen.sleepMicros(delay) --wait to reduce load

		--can modify packets here

		for _, buf in ipairs(bufs) do
			local pkt = buf:getUdpPacket()
	
			--set the destination ip and do a pseudo random jump to trigger caceh miss in the router
			pkt.ip4.dst:set(i)
			i = i + (CACHE_JUMP * (i+1));
			i = i % nbrRoutes

		end

		bufs:offloadUdpChecksums() -- harware checksums
	
		txQueue:send(bufs)
		txCtr:update()
	end
	txCtr:finalize()
end


--timestamps packets and gather stats
function timerSlave(txQueue, rxQueue, size, nbrRoutes)
	
	local timestamper = ts:newUdpTimestamper(txQueue, rxQueue)
	local hist = hist:new()
	local rateLimit = timer:new(0.001)

	i = 0
	
	while moongen.running() do
		hist:update(timestamper:measureLatency(size, function(buf)
			buf:getUdp4Packet():fill{
			pktLength = PACKET_SIZE,
			ethSrc = txQueue, -- device mac
			ethDst = " 90:e2:ba:55:14:39",--rxQueue,
			-- ipDst will be randomized later
			ip4Src = "10.0.0.1",
			udpSrc = 4321,
			udpDst = 1234,
		}

		local pkt = buf:getUdpPacket()

        --as in sendPackets
        pkt.ip4.dst:set(i)
        i = i + (CACHE_JUMP * (i+1))
        i = i % nbrRoutes

				
		end))

		rateLimit:wait()
		rateLimit:reset()
		
	end

	moongen.sleepMillis(300)
	hist:print()
	hist:save("histogram.csv")

end



