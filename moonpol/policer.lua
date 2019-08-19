--[[
This code is from Moonpol,
  "a scalable and high-performance traffic policer
   built on DPDK and LuaJIT via libmoon packet processing library."
https://github.com/erkinkirdan/moonpol

All changes have been clearly marked with CHANGE comments

License:
MIT License

Copyright (c) 2017 erkinkirdan

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
]]

-- CHANGE: Added 'os' dependency
local os      = require "os"
-- END CHANGE
local lm      = require "libmoon"
local device  = require "device"
local stats   = require "stats"
local memory  = require "memory"
local ffi     = require "ffi"

local BUCKET  = 2

ffi.cdef[[
  typedef struct {float tokens; uint32_t bucket_size;} subnet;
]]

local tbl24
local tbllong
local subnets
local subnetcounter
local round

function getsubnetid(ip)
  local a = bit.rshift(ip, 24)
  local b = bit.rshift(ip, 16) - bit.lshift(a, 8)
  local c = bit.rshift(ip, 8) - bit.lshift(b, 8) - bit.lshift(a, 16)
  local d = ip - bit.lshift(c, 8) - bit.lshift(b, 16) - bit.lshift(a, 24)
  local index1 = c + bit.lshift(b, 8) + bit.lshift(a, 16)
  if tbl24[index1] == 0 then
    return 0
  end
  if tbl24[index1] > 0 and tbl24[index1] % 10 == 0 then
    return tbl24[index1] / 10
  else
    local index2 = ((tbl24[index1] - 1) / 10) * 256 + d
    -- CHANGE: Don't divide by 10, related to changes in readconfig()
    return tbllong[index2]
    -- ENDCHANGE
  end
end

function removetoken(id)
  if id == 0 then
    return 1
  end
  if subnets[id].tokens >= 1 then
    subnets[id].tokens = subnets[id].tokens - 1
    return 1
  end
  return 0
end

function addtoken(interval)
  for  i = 1, subnetcounter do
    subnets[i].tokens = subnets[i].tokens +
      interval * subnets[i].bucket_size / BUCKET
    if subnets[i].tokens > subnets[i].bucket_size then
      subnets[i].tokens = subnets[i].bucket_size
    end
  end
end

function readconfig()
  local config = io.open("./config", "r")
  subnetcounter = 0
  local tmp0 = 0
  local tmp1 = 0
  while true do
    local line = config:read()
    if line == nil then
      break
    end
    subnetcounter = subnetcounter + 1
    for word in string.gmatch(line, '[^./	]+') do
      if tmp0 == 4 then
        if tonumber(word) > 24 then
          tmp1 = tmp1 + 1
        end
      end
      tmp0 = tmp0 + 1
      if tmp0 == 6 then
        tmp0 = 0
      end
    end
  end
  io.close(config)
  tbl24 = ffi.new("uint32_t[16777216]")
  tbllong = ffi.new("uint32_t[?]", tmp1 * 256)
  config = io.open("./config", "r")
  subnets = ffi.new("subnet[?]", (subnetcounter + 1))
  tmp0 = 0
  tmp1 = 1
  local tmp2 = 0
  while true do
    local line = config:read()
    if line == nil then
      break
    end
    local a, b, c, d, p, l
    for word in string.gmatch(line, '[^./	]+') do
      if tmp0 == 0 then
        a = tonumber(word)
      end
      if tmp0 == 1 then
        b = tonumber(word)
      end
      if tmp0 == 2 then
        c = tonumber(word)
      end
      if tmp0 == 3 then
        d = tonumber(word)
      end
      if tmp0 == 4 then
        p = tonumber(word)
      end
      if tmp0 == 5 then
        l = tonumber(word)
      end
      tmp0 = tmp0 + 1
      if tmp0 == 6  then
        tmp0 = 0
      end
    end
    if p < 25 then
      local index = c + bit.lshift(b, 8) + bit.lshift(a, 16)
      local space = 2 ^ (24 - p)
      for i = 0, space - 1 do
        tbl24[index + i] = tmp1 * 10
      end
    else
      -- CHANGE: Fix bugs with prefixes >= 25
      local tbl24index = c + bit.lshift(b, 8) + bit.lshift(a, 16)
      if tbl24[tbl24index] == 0 then
        tbl24[tbl24index] = tmp2 * 10 + 1
        tmp2 = tmp2 + 1
      end
      local index = ((tbl24[tbl24index] - 1) / 10) * 256 + d
      -- ENDCHANGE
      local space = 2 ^ (32 - p)
      for i = 0, space - 1 do
        -- CHANGE: Don't multiply by 10
        --         so we don't have to divide by 10 when processing packets
        tbllong[index + i] = tmp1
        -- ENDCHANGE
      end
      -- CHANGE: Part of the bugfix above is to move this line
      -- tmp2 = tmp2 + 1
      -- ENDCHANGE
    end
    subnets[tmp1].bucket_size = BUCKET * l
    subnets[tmp1].tokens = BUCKET * l
    tmp1 = tmp1 + 1
  end
  io.close(config)
end

function configure(parser)
  parser:option("-r --rounds", "Number of rounds."):args(1):
    convert(tonumber):default(1000000)
  -- CHANGE: Added batching switch
  parser:option("-b --batch", "Batch size."):convert(tonumber):default(1)
  -- ENDCHANGE
  return parser:parse()
end

function master(args)
  readconfig()
  -- CHANGE: Set the variables DST_MAC/SRC_MAC
  local DST_MAC = parseMacAddress("FF:FF:FF:FF:FF:FF", true)
  local SRC_MAC = parseMacAddress("00:00:00:00:00:00", true)
  -- END CHANGE
  round = args.rounds
  -- CHANGE: Use two devices instead of one
  local rxdev = device.config{port = 0}
  local txdev = device.config{port = 1}
  -- END CHANGE
  device.waitForLinks()
  -- CHANGE: Do not use statistics
  --stats.startStatsTask{dev}
  -- END CHANGE
  -- CHANGE: Use device 0 for RX, 1 for TX instead of 0 for both
  local rxQ = rxdev:getRxQueue(0)
  local txQ = txdev:getTxQueue(0)
  -- END CHANGE
  local rxBufs = memory.bufArray()
  local txBufs = memory.bufArray()
  local tokenlast = lm.getTime()
  local tokeninterval
  local roundctr = 0
  local batchSize = 1
  while lm.running() do
    -- CHANGE: Use args.batch instead of leaving the default second argument
    local rx = rxQ:recv(rxBufs, args.batch)
    -- END CHANGE
    local j = 0
    for i = 1, rx do
      local id = getsubnetid(rxBufs[i]:getUdpPacket().ip4:getSrc())
      if removetoken(id) > 0 then
        j = j + 1
        txBufs[j] = rxBufs[i]
        local pkt = txBufs[j]:getUdpPacket()
        pkt.eth:setDst(DST_MAC)
        pkt.eth:setSrc(SRC_MAC)
      else
        -- CHANGE: Exit if we reach here, we don't want to actually police since this is a benchmark baseline!
        os.exit(1)
        -- ENDCHANGE
        rxBufs[i]:free()
      end
    end
    txQ:sendN(txBufs, j)
    roundctr = roundctr + 1
    if roundctr >= round then
      tokeninterval = lm.getTime() - tokenlast
      tokenlast = lm.getTime()
      addtoken(tokeninterval)
      roundctr = 0
    end
  end
  lm.waitForTasks()
end
