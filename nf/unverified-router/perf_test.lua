local device = require "device"
local moongen = require "moongen"
local memory = require "memory"
local arp    = require "proto.arp"
local stats  = require "stats"


local NB_DIFF_IP4 = 10

function master(txNum, rxNum)


	txDev = device.config{	--configure device for transmission

		port = txNum,
		rxQueues = 1,
		txQueues = 1,
	}

	rxDev = device.config{	--configure device for reception

		port = rxNum,
		rxQueues = 1,
		txQueues = 1,
	}

	device.waitForLinks()	--wait for the devices


	local arrayIp4 = {}		--prepare NB_DIFF_IP4 ip addresses

	for i = 0, NB_DIFF_IP4 -1 do
		arrayIp4[i] = getRandomIp4()
	end

	moongen.startTask("receivePackets", rxDev:getRxQueue(0), rxDev)		--launch slave task for reception
	moongen.startTask("sendPackets", txDev:getTxQueue(0), arrayIp4)--, rxDev:getRxQueue(0), arrayIp4)		--launch slave task for transmission


	moongen.waitForTasks() -- wait for child termination
	

end




function receivePackets(rxQueue, rxDev)

	local bufs = memory.bufArray()
	local rxCtr = stats:newDevRxCounter(rxQueue.dev)

	while moongen.running() do

		local rx = rxQueue:recv(bufs)

		for i = 1, rx do

			local pkt = bufs[i]:getUdp4Packet()
			--print("Packet: " .. pkt.ip4:getString())
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
			pktLength = 128,
			ethSrc = txQueue, -- device mac
			ethDst = "00:64:74:61:70:00",--rxQueue,
			-- ipDst will be randomized later
			--ip4Dst = "10.0.0.2",
			ip4Src = "10.0.0.1",
			udpSrc = 4321,
			udpDst = 1234,
		}

	end)

	local bufs = mem:bufArray()
	
	i = 0

	while moongen.running() do
		bufs:alloc(250) --allocate memory for packets

		--can modify packets here

		for _, buf in ipairs(bufs) do
			local pkt = buf:getUdpPacket()
	
			pkt.ip4.dst:set(parseIPAddress(arrayIp4[i])) -- select an ipDst
			i = (i + 1) % NB_DIFF_IP4 
		end

		bufs:offloadUdpChecksums() -- harware checksums
	
		txQueue:send(bufs)
		txCtr:update()
	end
	txCtr:finalize()
end
