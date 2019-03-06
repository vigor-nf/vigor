open Str
open Core
open Fspec_api
open Ir
open Common_fspec

let ip_addr_struct = Ir.Str ( "ip_addr", ["addr", Uint32;])
let dynamic_value_struct = Ir.Str ( "DynamicValue", ["bucket_size", Uint32;
                                                     "bucket_time", vigor_time_t;] )
(* FIXME: borrowed from ../nf/vigpolicer/policer_data_spec.ml *)
let containers = ["dyn_map", Map ("ip_addr", "capacity", "");
                  "dyn_keys", Vector ("ip_addr", "capacity", "");
                  "dyn_heap", DChain "capacity";
                  "dyn_vals", Vector ("DynamicValue", "capacity", "");
                  "capacity", UInt32;
                  "dev_count", UInt32;
                  "", EMap ("ip_addr", "dyn_map", "dyn_keys", "dyn_heap");
                 ]

let records = String.Map.of_alist_exn
                ["ip_addr", ip_addr_struct;
                 "DynamicValue", dynamic_value_struct]

(* TODO: make external_ip symbolic *)
module Iface : Fspec_api.Spec =
struct
  let preamble = gen_preamble "vigpolicer/policer_loop.h" containers
  let fun_types = fun_types containers records
  let boundary_fun = "loop_invariant_produce"
  let finishing_fun = "loop_invariant_consume"
  let eventproc_iteration_begin = "loop_invariant_produce"
  let eventproc_iteration_end = "loop_invariant_consume"
  let user_check_for_complete_iteration = In_channel.read_all "policer_forwarding_property.tmpl"
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

