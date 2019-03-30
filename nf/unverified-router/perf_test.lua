local device = require "device"
local moongen = require "moongen"
local memory = require "memory"
local arp    = require "proto.arp"
local stats  = require "stats"

-- best config 10000, 8, 1
--local NB_DIFF_IP4 = 10000;
local NB_TX_QUEUE = 1;
local NB_RX_QUEUE = 1;

function master(txNum)


	txDev = device.config{	--configure device for transmission

		port = txNum,
		rxQueues = NB_RX_QUEUE,
		txQueues = NB_TX_QUEUE,	
	}

	--rxDev = device.config{	--configure device for reception

	--	port = rxNum,
	--	rxQueues = 1,
	--	txQueues = 1,
	--}

	device.waitForLinks()	--wait for the devices


	local arrayIp4 = {}		--prepare NB_DIFF_IP4 ip addresses

--	for i = 0, NB_DIFF_IP4 -1 do
--		arrayIp4[i] = getRandomIp4()
--	end
	
	for i = 0, NB_RX_QUEUE -1 do
		moongen.startTask("receivePackets", txDev:getRxQueue(i))		--launch slave task for reception
	end

	for i = 0, NB_TX_QUEUE -1 do

		moongen.startTask("sendPackets", txDev:getTxQueue(i), arrayIp4)--, rxDev:getRxQueue(0), arrayIp4)		--launch slave task for transmission
	end

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



function sendPackets(txQueue, arrayIp4)

 	local txCtr = stats:newDevTxCounter(txQueue, "plain")

	local mem = memory.createMemPool(function(buf)	--fill the packet before to increase performance
		buf:getUdp4Packet():fill{
			pktLength = 52,
			ethSrc = txQueue, -- device mac
			ethDst = " 90:e2:ba:55:14:39",--rxQueue,
			-- ipDst will be randomized later
			--ip4Dst = "10.0.0.2", --remove when randomizing
	--		ip4Src = "10.0.0.1",
	--		udpSrc = 4321,
	--		udpDst = 1234,
		}

	end)

	local bufs = mem:bufArray()
	
	i = 0

	while moongen.running() do
		bufs:alloc(52) --allocate memory for packets
		
		
		--for i = 0, 10000000000 do --busy waiting
		--end

		--can modify packets here

		for _, buf in ipairs(bufs) do
			local pkt = buf:getUdpPacket()
	
			--pkt.ip4.dst:set(parseIPAddress(arrayIp4[i])) -- select an ipDst
			--i = (i + 1) % NB_DIFF_IP4 
			pkt.ip4.dst:set(i)
			i = i + 1
		--	print("Packet: " .. pkt.ip4:getString())
		end

		bufs:offloadUdpChecksums() -- harware checksums
	
		txQueue:send(bufs)
		txCtr:update()
	end
	txCtr:finalize()
end
