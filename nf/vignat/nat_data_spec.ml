open Data_spec

let containers = ["fm", Map ("FlowId", "max_flows");
                  "fv", Vector ("FlowId", "max_flows");
                  "heap", DChain "max_flows";
                  "max_flows", Int;
                  "start_port", Int;
                  "ext_ip", UInt32;
                  "", EMap ("FlowId", "fm", "fv", "heap")]

let header_fname = "nat_loop.h"
let stub_fname = "nat_loop.c"
let custom_includes = ["flow.h.gen.h"]
