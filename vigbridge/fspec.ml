open Str
open Core
open Fspec_api
open Ir
open Common_fspec

let static_key_struct = Ir.Str ( "StaticKey", ["addr", rte_ether_addr_struct;
                                               "device", Uint16] )
let dynamic_value_struct = Ir.Str ( "DynamicValue", ["device", Uint16] )

(* TODO: make external_ip symbolic *)
module Iface : Fspec_api.Spec =
struct
(* FIXME: borrowed from ../nf/vigbridge/bridge_data_spec.ml*)
let containers = ["dyn_map", Map ("rte_ether_addr", "capacity", "");
                  "dyn_keys", Vector ("rte_ether_addr", "capacity", "");
                  "dyn_vals", Vector ("DynamicValue", "capacity", "dyn_val_condition");
                  "st_map", Map ("StaticKey", "stat_capacity", "stat_map_condition");
                  "st_vec", Vector ("StaticKey", "stat_capacity", "");
                  "dyn_heap", DChain "capacity";
                  "capacity", UInt32;
                  "stat_capacity", UInt32;
                  "dev_count", UInt32;
                  "dyn_emap", EMap ("rte_ether_addr", "dyn_map", "dyn_keys", "dyn_heap")]

let records = String.Map.of_alist_exn
    ["rte_ether_addr", rte_ether_addr_struct;
     "DynamicValue", dynamic_value_struct;
     "StaticKey", static_key_struct]
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

