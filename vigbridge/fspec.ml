open Str
open Core
open Fspec_api
open Ir
open Common_fspec

let static_key_struct = Ir.Str ( "StaticKey", ["addr", ether_addr_struct;
                                               "device", Uint16] )
let dynamic_value_struct = Ir.Str ( "DynamicValue", ["device", Uint16] )

(* FIXME: borrowed from ../nf/vigbridge/bridge_data_spec.ml*)
let containers = ["dyn_map", Map ("ether_addr", "capacity", "");
                  "dyn_keys", Vector ("ether_addr", "capacity", "");
                  "dyn_vals", Vector ("DynamicValue", "capacity", "dyn_val_condition");
                  "st_map", Map ("StaticKey", "stat_capacity", "stat_map_condition");
                  "st_vec", Vector ("StaticKey", "stat_capacity", "");
                  "dyn_heap", DChain "capacity";
                  "capacity", UInt32;
                  "stat_capacity", UInt32;
                  "dev_count", UInt32;
                  "dyn_emap", EMap ("ether_addr", "dyn_map", "dyn_keys", "dyn_heap")]

let records = String.Map.of_alist_exn
    ["ether_addr", ether_addr_struct;
     "DynamicValue", dynamic_value_struct;
     "StaticKey", static_key_struct]

(* TODO: make external_ip symbolic *)
module Iface : Fspec_api.Spec =
struct
  let preamble = gen_preamble "vigbridge/bridge_loop.h" containers
  let fun_types = fun_types containers records
  let boundary_fun = "loop_invariant_produce"
  let finishing_fun = "loop_invariant_consume"
  let eventproc_iteration_begin = "loop_invariant_produce"
  let eventproc_iteration_end = "loop_invariant_consume"
  let user_check_for_complete_iteration =
    (abstract_state_capture containers) ^
    (In_channel.read_all "bridge_forwarding_property.tmpl")
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

