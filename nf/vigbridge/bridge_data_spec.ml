open Data_spec

let containers = ["dyn_map", Map ("ether_addr", "capacity", "");
                  "dyn_keys", Vector ("ether_addr", "capacity", "");
                  "dyn_vals", Vector ("DynamicValue", "capacity", "dyn_val_condition");
                  "st_map", Map ("StaticKey", "stat_capacity", "stat_map_condition");
                  "st_vec", Vector ("StaticKey", "stat_capacity", "");
                  "dyn_heap", DChain "capacity";
                  "capacity", UInt32;
                  "stat_capacity", UInt32;
                  "dev_count", UInt32;
                  "", EMap ("ether_addr", "dyn_map", "dyn_keys", "dyn_heap")]

let loop_header_fname = "bridge_loop.h"
let state_header_fname = "bridge_state.h"
let loop_stub_fname = "bridge_loop.c"
let state_fname = "bridge_state.c"
let custom_includes = ["stat_key.h.gen.h";
                       "dyn_value.h.gen.h"]
