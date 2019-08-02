open Data_spec

let containers = ["fm", Map ("FlowId", "max_flows", "");
                  "fv", Vector ("FlowId", "max_flows", "");
                  "int_devices", Vector ("uint32_t", "max_flows", "int_dev_bounds");
                  "heap", DChain "max_flows";
                  "max_flows", Int;
                  "fw_device", UInt32;
                  "flow_emap", EMap ("FlowId", "fm", "fv", "heap")]

let loop_header_fname = "fw_loop.h"
let state_header_fname = "fw_state.h"
let loop_stub_fname = "fw_loop.c"
let state_fname = "fw_state.c"
let custom_includes = ["flow.h.gen.h"]
