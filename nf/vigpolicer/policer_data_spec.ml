open Data_spec

let containers = ["dyn_heap", DChain "capacity";
                  "dyn_map", Map ("ip_addr", "capacity");
                  "dyn_keys", Vector ("ip_addr", "capacity");
                  "dyn_vals", Vector ("DynamicValue", "capacity");
                  "capacity", UInt32;
                  "dev_count", UInt32;
                  "", EMap ("ip_addr", "dyn_map", "dyn_keys", "dyn_heap");
                 ]

let header_fname = "policer_loop.h"
let stub_fname = "policer_loop.c"
let custom_includes = ["dynamic_value.h.gen.h";
                       "ip_addr.h.gen.h"]
