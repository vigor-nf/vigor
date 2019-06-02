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

--enter the nic number (port) and the delay between tx packets (to reduce load)
function master(nic, delay)

	print("Try to configure devices")

	--configure the device 
	dev = device.config{	

		port = nic,
		rxQueues = NB_RX_QUEUE,
		txQueues = NB_TX_QUEUE,	
	}

	
	--wait for the devices
	device.waitForLinks()	

	--launch slave task for reception
	moongen.startTask("receivePackets", dev:getRxQueue(0))		

	--launch slave task for transmission
	moongen.startTask("sendPackets", dev:getTxQueue(0), delay)
	
	-- launch slave task for timestamping
	moongen.startTask("timerSlave", dev:getTxQueue(1), dev:getRxQueue(1), PACKET_SIZE) 


	moongen.waitForTasks() -- wait for child termination
	

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


--send packets with a fix destination ip (triggers cache hit in the nf)
function sendPackets(txQueue, delay)

 	local txCtr = stats:newDevTxCounter(txQueue, "plain")

	local mem = memory.createMemPool(function(buf)	--fill the packet before to increase performance
		buf:getUdp4Packet():fill{
			pktLength = PACKET_SIZE,
			ethSrc = txQueue, -- device mac
			ethDst = " 90:e2:ba:55:14:39",--rxQueue,
			ip4Dst = "10.0.0.2", --remove when randomizing
		}

	end)

	local bufs = mem:bufArray()
	
	i = 0

	while moongen.running() do
		bufs:alloc(PACKET_SIZE) --allocate memory for packets
		
		--delay packet generation to reduce load
		moongen.sleepMicros(delay)

		bufs:offloadUdpChecksums() -- harware checksums
	
		txQueue:send(bufs)
		txCtr:update()
	end
	txCtr:finalize()
end


--timestamp packets and gather stats
function timerSlave(txQueue, rxQueue, size)
	
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
			ip4Dst = "10.0.0.2", --remove when randomizing

		}
	
		end))

		rateLimit:wait()
		rateLimit:reset()
		
	end

	moongen.sleepMillis(300)
	hist:print()
	hist:save("histogram.csv")

end




