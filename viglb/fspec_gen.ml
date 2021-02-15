open Data_spec
open Core
open Ir

let containers = ["flow_to_flow_id", Map ("LoadBalancedFlow", "flow_capacity",
                                          "lb_flow_id_condition");
                  "flow_heap", Vector ("LoadBalancedFlow", "flow_capacity", "");
                  "flow_chain", DChain "flow_capacity";
                  "flow_id_to_backend_id", Vector ("uint32_t", "flow_capacity",
                                                   "lb_flow_id2backend_id_cond");
                  "ip_to_backend_id", Map ("ip_addr", "backend_capacity",
                                           "lb_backend_id_condition");
                  "backend_ips", Vector ("ip_addr", "backend_capacity", "");
                  "backends", Vector ("LoadBalancedBackend", "backend_capacity",
                                      "lb_backend_condition");
                  "active_backends", DChain "backend_capacity";
                  "cht", CHT ("backend_capacity", "cht_height");
                  "backend_capacity", UInt32;
                  "flow_capacity", UInt32;
                  "cht_height", UInt32;
                  "", EMap ("LoadBalancedFlow", "flow_to_flow_id", "flow_heap",
                            "flow_chain");
                  "", EMap ("ip_addr", "ip_to_backend_id", "backend_ips",
                            "active_backends");
                 ]

let constraints = ["lb_backend_id_condition",
                   ( "ip_addr",
                     [Bop (Le, {t=Unknown;v=Int 0}, {t=Unknown;v=Id "index"});
                      Bop (Lt, {t=Unknown;v=Id "index"}, {t=Unknown;v=Int 32});
                     ]);
                   "lb_flow_id_condition",
                   ( "LoadBalancedFlow",
                     [Bop (Le, {t=Unknown;v=Int 0}, {t=Unknown;v=Id "index"});
                      Bop (Lt, {t=Unknown;v=Id "index"}, {t=Unknown;v=Int 65536});
                     ]);
                   "lb_backend_condition",
                   ( "LoadBalancedBackend",
                     [Bop (Le, {t=Unknown;v=Int 0}, {t=Unknown;v=Id "nic"});
                      Bop (Lt, {t=Unknown;v=Id "nic"}, {t=Unknown;v=Int 3});
                      Not {v=Bop (Eq, {t=Unknown;v=Id "nic"}, {t=Unknown;v=Int 2});
                           t=Unknown};
                     ]);
                   "lb_flow_id2backend_id_cond",
                   ( "uint32_t",
                     [Bop (Lt, {t=Unknown;v=Id "v"}, {t=Unknown;v=Int 32});
                     ])]

let gen_custom_includes = ref []
let gen_records = ref []
let () = 
  gen_records := ("LoadBalancedFlow", (Ir.Str ("LoadBalancedFlow", ["src_ip", Ir.Uint32; "dst_ip", Ir.Uint32; "src_port", Ir.Uint16; "dst_port", Ir.Uint16; "protocol", Ir.Uint8])))::!gen_records

let () = 
  gen_custom_includes := "lb_flow.h.gen.h"::!gen_custom_includes

let () = 
  gen_records := ("LoadBalancedBackend", (Ir.Str ("LoadBalancedBackend", ["nic", Ir.Uint16; "mac", Ir.Str("rte_ether_addr", ["addr_bytes", Ir.Array (Ir.Uint8)]); "ip", Ir.Uint32])))::!gen_records

let () = 
  gen_custom_includes := "lb_backend.h.gen.h"::!gen_custom_includes

let () = 
  gen_records := ("ip_addr", (Ir.Str ("ip_addr", ["addr", Ir.Uint32])))::!gen_records

let () = 
  gen_custom_includes := "ip_addr.h.gen.h"::!gen_custom_includes

