open Data_spec
open Core
open Ir

let containers = ["fm", Map ("FlowId", "max_flows", "");
                  "fv", Vector ("FlowId", "max_flows", "flow_consistency");
                  "heap", DChain "max_flows";
                  "max_flows", Int;
                  "start_port", Int;
                  "ext_ip", UInt32;
                  "nat_device", UInt32;
                  "flow_emap", EMap ("FlowId", "fm", "fv", "heap")]

let constraints = ["flow_consistency", ( "FlowId",
                                         [Bop (Le, {t=Unknown;v=Int 0}, {t=Unknown;v=Id "internal_device"});
                                          Bop (Lt, {t=Unknown;v=Id "internal_device"}, {t=Unknown;v=Int 2});
                                          Not {v=Bop (Eq, {t=Unknown;v=Id "internal_device"}, {t=Unknown;v=Int 1});
                                               t=Unknown};
                                         ])]

let gen_custom_includes = ref []
let gen_records = ref []
