open Data_spec

let containers = ["dyn_map", Map ("ip_addr", "capacity", "");
                  "dyn_keys", Vector ("ip_addr", "capacity", "");
                  "dyn_heap", DChain "capacity";
                  "dyn_vals", Vector ("DynamicValue", "capacity", "");
                  "capacity", UInt32;
                  "dev_count", UInt32;
                  "flow_emap", EMap ("ip_addr", "dyn_map", "dyn_keys", "dyn_heap");
                 ]

let loop_header_fname = "policer_loop.h"
let state_header_fname = "policer_state.h"
let loop_stub_fname = "policer_loop.c"
let state_fname = "policer_state.c"
let custom_includes = ["dynamic_value.h.gen.h";
                       "ip_addr.h.gen.h"]
