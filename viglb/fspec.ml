open Str
open Core
open Fspec_api
open Ir
open Common_fspec

let lb_flow_struct = Ir.Str ( "LoadBalancedFlow", ["src_ip", Uint32;
                                                   "dst_ip", Uint32;
                                                   "src_port", Uint16;
                                                   "dst_port", Uint16;
                                                   "protocol", Uint8;])
let lb_backend_struct = Ir.Str ( "LoadBalancedBackend", ["nic", Uint16;
                                                         "mac", rte_ether_addr_struct;
                                                         "ip", Uint32])

let ip_addr_struct = Ir.Str("ip_addr", ["addr", Uint32])


module Iface : Fspec_api.Spec =
struct
(* FIXME: borrowed from ../nf/vigbalancer/lb_data_spec.ml*)
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
                  "flow_emap", EMap ("LoadBalancedFlow", "flow_to_flow_id",
                                     "flow_heap", "flow_chain");
                  "backend_ip_emap", EMap ("ip_addr", "ip_to_backend_id",
                                           "backend_ips", "active_backends");
                 ]

let records = String.Map.of_alist_exn
    ["LoadBalancedFlow", lb_flow_struct;
     "ip_addr", ip_addr_struct;
     "uint32_t", Uint32;
     "LoadBalancedBackend", lb_backend_struct]
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

