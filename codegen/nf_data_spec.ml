open Data_spec

let containers = ["dyn_map", Map ("ether_addr", "capacity");
                  "dyn_keys", Vector ("ether_addr", "capacity");
                  "dyn_vals", Vector ("DynamicValue", "capacity");
                  "st_map", Map ("StaticKey", "_");
                  "st_vec", Vector ("StaticKey", "");
                  "dyn_heap", DChain "capacity";
                  "capacity", UInt32;
                  "dev_count", UInt32;
                  "", EMap ("ether_addr", "dyn_map", "dyn_keys", "dyn_heap")]

let header_fname = "bridge_loop.h"
let stub_fname = "bridge_loop.c"
let custom_includes = ["stat_key.h.gen.h";
                       "dyn_value.h.gen.h"]
