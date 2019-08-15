package.path = package.path .. ";" .. "/usr/share/lua/5.1/?.lua"
package.cpath = package.cpath .. ";" .. "/usr/lib/x86_64-linux-gnu/lua/5.1/?.so"
function script_path()
   local str = debug.getinfo(2, "S").source:sub(2)
   return str:match("(.*/)")
end
package.path = package.path .. ";" .. script_path() .. "/?.lua"

local dpdk		= require "dpdk"
local device	= require "device"
local lpm     = require "lpm"
local distribute = require "distribute"
local l3arp = require "l3SyncArp"
local pipe = require "pipe"

local ui = require("userInterface")
local slowPath = require("slowPath")
local fastPath = require("fastPath")

local kni = require("kni")
local memory = require("memory")

function getNumber(table)
  local i = 0
  for _,_ in pairs(table) do
    i = i + 1
  end
  return i
end

--- Initializes the router
-- freq == 1  ==> minimum frequency
function master(freq, ...)
 
  local config = dofile "../MoonRoute/cfg.lua"
 

  printfColor("Assigning devices to cores...", "yellow")
  for _, port in pairs(config.ports) do
    port["device"] = device.get(port.mac)
    if(port.device == nil) then
      errorf("ERROR: device with mac %s not found", port.mac)
    end
  end

  -- cores will contain a list of ports and queues for each cpu core
  local cores = {}
  config["nrPorts"] = 0
  local outputSeqNr = 0
  for _, port in pairs(config.ports) do
    config.nrPorts = config.nrPorts + 1
    if(port.direction == "inout" or port.direction == "out")then
      port["outputSeqNr"] = outputSeqNr
      outputSeqNr = outputSeqNr + 1
    end
    if(port.direction == "inout" or port.direction == "in")then
      port.fastPathCores = port.fastPathCores or config.fastPathCores
      --port.rxBurstSize = port.rxBurstSize or config.rxBurstSize
      local i = 0
      for _, c in ipairs(port.fastPathCores) do
        printf("core %d -> mac: %s", c, port.mac)
        cores[c] = cores[c] or {}
        cores[c]["ports"] = cores[c]["ports"] or {}
        cores[c]["ports"][getNumber(cores[c]["ports"])+1] = port
        -- every core gets one rx queue for each assigned port
        cores[c]["rxQueues"] = cores[c]["rxQueues"] or {}
        cores[c]["rxQueues"][getNumber(cores[c]["rxQueues"])+1] = port.device:getRxQueue(i)
        i = i + 1
      end
    end
  end

  -- configure the devices:
  printfColor("Configuring devices...", "yellow")
  for _, port in pairs(config.ports) do
    printf(" configuring %s", port.mac)
    port["direction"] = port["direction"] or "inout"
    if(port.direction == "out") then
      errorf("out devices currently not supported")
    elseif(port.direction == "in") then
      errorf("in devices currently not supported")
      
    else
      local rxDescsS = 4*config.rxBurstSize
      local txDescsS = 4*config.txQueueSize
      if(rxDescsS < 4*128) then
        rxDescsS = 4*128
      end
      if(txDescsS < 4*64) then
        txDescsS = 4*64
      end
      device.config({
        port=port.device.id,
        rxQueues=1+1+getNumber(port.fastPathCores),
        txQueues=1+1+getNumber(cores),
        rssNQueues=getNumber(port.fastPathCores),
        rxDescs = rxDescsS,
        txDescs = rxDescsS,
        separateMemPools=true,
       
        memPoolSize = 2*rxDescsS + config.nrPorts * txDescsS + config.slowPathQueueSize + 1
       
        })
    end
  end

  printfColor("Waiting for devices to come up...", "yellow")
  device.waitForLinks();

  printfColor("Initializing ARP...", "yellow")
  for _, port in pairs(config.ports) do
    port["arpRxQueue"] = port.device:getRxQueue(1+1+getNumber(port.fastPathCores) - 1)
    port["arpTxQueue"] = port.device:getTxQueue(1+1+getNumber(cores) - 1)
  end
  local arpInstance = l3arp.createSyncArp(config)
  config["arpInstance"] = arpInstance

  local lpmTable = lpm.createLpm4Table()
  printfColor("Configuring initial routes...", "yellow")
  lpmTable:addRoutesFromTable(config.routes, config.ports, function(ip) return config.arpInstance:blockingLookup(ip, 0.5) end)

  -- start fast path units
  printfColor("Starting Fast Path units...", "yellow")
  local i = 1
  for c, core in pairs(cores) do
    local distributor = distribute.createDistributor(nil, nil, config.nrPorts, false)
    -- register all output ports
    for _, port2 in pairs(config.ports) do
      if(port2.direction == "inout" or port2.direction == "out")then
        distributor:registerOutput(port2.outputSeqNr,
        port2.device:getTxQueue(i),
        port2.txQueueSize or config.txQueueSize,
        port2.txQueueTimeout or config.txQueueTimeout)
      end
    end
    -- create the queues for communicating with the slow path:
    local slowQueue = pipe.newFastCPipe({size = config.slowPathQueueSize})
    core["slowQueue"] = slowQueue
    local cmdRxQueue = pipe.newSlowPipe()
    core["cmdRxQueue"] = cmdRxQueue
    local cmdTxQueue = pipe.newSlowPipe()
    core["cmdTxQueue"] = cmdTxQueue
    -- TODO: NUMA awareness
    printf("  Launch FastPath on core %d...", c)
    local testports = {}

    testports = {config.ports["Port1"].device:getTxQueue(i) }
   
    dpdk.launchLuaOnCore(c, "runFastPath", lpmTable, distributor,
      core.rxQueues,
      slowQueue,
      cmdRxQueue,
      cmdTxQueue,
      config.rxBurstSize, c, testports )
    i = i+1
  end

  -- enable the telnet interface:
  config["dynamicRoutes"] = {}
  local telnetUi
  if(config.telnetEnable) then
    printfColor("Initializing telnet user interface...", "yellow")
    telnetUi = ui.createUserInterface(config)
  end

  -- start slow path unit
  printfColor("Initializing Slow Path for core 0...", "yellow")
  -- Now we set up the slow path:
  local distributor = distribute.createDistributor(nil, nil, config.nrPorts, false)
  -- register all output ports
  for _, port2 in pairs(config.ports) do
    if(port2.direction == "inout" or port2.direction == "out")then
      distributor:registerOutput(port2.outputSeqNr,
        port2.device:getTxQueue(1+1+getNumber(cores) - 1 - 1),
        port2.txQueueSize or config.txQueueSize,
        port2.txQueueTimeout or config.txQueueTimeout)
    end
  end
  local slowPathInstance = slowPath.createSlowPath(cores, config, lpmTable, distributor)
  
  if(config["enableVirtualInterfaces"]) then
    printfColor("Creating virtual interfaces...", "yellow")
    config["virtualInterfacePrefix"] = config["virtualInterfacePrefix"] or "mgVEth-"
    config["virtualDevices"] = {}
    -- FIXME: why does kni need such a big mempool???
    --  if it is samller i get lots of error messages "out of memory"
    local virtualDevMemPool = memory.createMemPool({n=8192})
    for p_name, port in pairs(config.ports) do
      printf("creating %s%s", config.virtualInterfacePrefix, p_name)
      config.virtualDevices[config.virtualInterfacePrefix .. p_name] = p_name
      port["virtualDev"] = kni.createKNI(0, port.device, virtualDevMemPool, config.virtualInterfacePrefix .. p_name)
      -- configure the virtual interface
      -- FIXME: this is ugly, but I have no time to make it better
      --  please forgive me
      io.popen("/sbin/ifconfig " .. config.virtualInterfacePrefix .. p_name .. " " .. port.ipv4 .. "/" .. port.ipv4Prefix)
      -- give the interface 100ms time to respond to the configuration request:
      for i = 0, 100 do
        port.virtualDev:handleRequest()
        dpdk.sleepMillisIdle(1)
      end
    end
  end

  printfColor("------------------", "green")
  printfColor(">> Router ready <<", "green")
  printfColor("------------------", "green")

  --local virtMem = memory.createMemPool({n=64})
  local virtMem = memory.createMemPool()
  local virtBufs = virtMem:bufArray(16)


  dpdk.waitForSlaves()
end

function runFastPath(...)
  fastPath.run(...)
end
