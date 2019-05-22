local device = require "device"
local moongen = require "moongen"
local memory = require "memory"
local arp    = require "proto.arp"
local stats  = require "stats"
local ts     = require "timestamping"
local filter = require "filter"
local hist   = require "histogram"
local timer  = require "timer"


-- best config 10000, 8, 1
--local NB_DIFF_IP4 = 10000;
local NB_TX_QUEUE = 2;
local NB_RX_QUEUE = 2;
local PACKET_SIZE = 84;

function master(txNum, delay)

	print("Try to configure devices")

	txDev = device.config{	--configure device for transmission

		port = txNum,
		rxQueues = NB_RX_QUEUE,
		txQueues = NB_TX_QUEUE,	
	}

	

	device.waitForLinks()	--wait for the devices


	local arrayIp4 = {}		--prepare NB_DIFF_IP4 ip addresses


		moongen.startTask("receivePackets", txDev:getRxQueue(0))		--launch slave task for reception
	

	
		moongen.startTask("sendPackets", txDev:getTxQueue(0), delay)	--launch slave task for transmission

	moongen.startTask("timerSlave", txDev:getTxQueue(1), txDev:getRxQueue(1), PACKET_SIZE)

	moongen.waitForTasks() -- wait for child termination
	


end


function receivePackets(rxQueue)

	local bufs = memory.bufArray()
	local rxCtr = stats:newDevRxCounter(rxQueue.dev)

	while moongen.running() do

		local rx = rxQueue:recv(bufs)

		for i = 1, rx do 

	--		local pkt = bufs[i]:getUdp4Packet()
	--		print("Packet: " .. pkt.ip4:getString())
			--print("from ip: " .. pkt.ip4.dst:getString())
		end
		rxCtr:update()
		bufs:freeAll()
	end
		rxCtr:finalize()

end



function getRandomIp4()		--generates random ipv4 addresses

	local s = ""

	for i = 0 , 3 do
		if(i ~= 0) then
			s = s .. "."
		end
		s = s .. math.random(0,255)
	end

return s
end



function sendPackets(txQueue, delay)

 	local txCtr = stats:newDevTxCounter(txQueue, "plain")

	local mem = memory.createMemPool(function(buf)	--fill the packet before to increase performance
		buf:getUdp4Packet():fill{
			pktLength = PACKET_SIZE,
			ethSrc = txQueue, -- device mac
			ethDst = " 90:e2:ba:55:14:39",--rxQueue,
	--		 ipDst will be randomized later
			ip4Dst = "10.0.0.2", --remove when randomizing
	--		ip4Src = "10.0.0.1",
	--		udpSrc = 4321,
	--		udpDst = 1234,
		}

	end)

	local bufs = mem:bufArray()
	
	i = 0

	while moongen.running() do
		bufs:alloc(PACKET_SIZE) --allocate memory for packets
		
		
		moongen.sleepMicros(delay)


		--can modify packets here

		--for _, buf in ipairs(bufs) do
		--	local pkt = buf:getUdpPacket()
	
			--pkt.ip4.dst:set(parseIPAddress(arrayIp4[i])) -- select an ipDst
			--i = (i + 1) % NB_DIFF_IP4 
		--	pkt.ip4.dst:set(i)
		--	i = i + 1

		--	print("Packet: " .. pkt.ip4:getString())
		--end

		bufs:offloadUdpChecksums() -- harware checksums
	
		txQueue:send(bufs)
		txCtr:update()
	end
	txCtr:finalize()
end



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
			-- ipDst will be randomized later
			ip4Dst = "10.0.0.2", --remove when randomizing
	--		ip4Src = "10.0.0.1",
	--		udpSrc = 4321,
	--		udpDst = 1234,
		}
	
	 


	--	local pkt = buf:getUdpPacket()

                        --pkt.ip4.dst:set(parseIPAddress(arrayIp4[i])) -- select an ipDst
                --i = (i + 1) % NB_DIFF_IP4 
          --      pkt.ip4.dst:set(i)
            --    i = i + 1
	--	 moongen.sleepMillis(1)

		end))

		rateLimit:wait()
		rateLimit:reset()
		
	end

	moongen.sleepMillis(300)
	hist:print()
	hist:save("histogram.csv")

end




