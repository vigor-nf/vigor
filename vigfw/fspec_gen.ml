open Data_spec
open Core
open Ir

let containers = ["fm", Map ("FlowId", "max_flows", "");
                  "fv", Vector ("FlowId", "max_flows", "");
                  "int_devices", Vector ("uint32_t", "max_flows", "int_dev_bounds");
                  "heap", DChain "max_flows";
                  "max_flows", Int;
                  "fw_device", UInt32;
                  "flow_emap", EMap ("FlowId", "fm", "fv", "heap")]

let constraints = ["int_dev_bounds", ( "uint32_t",
                                         [Bop (Lt, {t=Unknown;v=Id "v"}, {t=Unknown;v=Int 2});
                                          Not {v=Bop (Eq, {t=Unknown;v=Id "v"}, {t=Unknown;v=Int 1});
                                               t=Unknown};
                                         ])]

let gen_custom_includes = ref []
let gen_records = ref []
let () = 
  gen_records := ("FlowId", (Ir.Str ("FlowId", ["src_port", Ir.Uint16; "dst_port", Ir.Uint16; "src_ip", Ir.Uint32; "dst_ip", Ir.Uint32; "protocol", Ir.Uint8])))::!gen_records

let () = 
  gen_custom_includes := "flow.h.gen.h"::!gen_custom_includes

