open Data_spec

let containers = ["fm", Map ("FlowId", "max_flows", "");
                  "fv", Vector ("FlowId", "max_flows", "flow_consistency");
                  "heap", DChain "max_flows";
                  "max_flows", Int;
                  "start_port", Int;
                  "ext_ip", UInt32;
                  "nat_device", UInt32;
                  "flow_emap", EMap ("FlowId", "fm", "fv", "heap")]

let custom_includes = ["flow.h.gen.h"]
