open Str
open Core
open Fspec_api
open Ir
open Common_fspec

let ip_addr_struct = Ir.Str ( "ip_addr", ["addr", Uint32;])
let dynamic_value_struct = Ir.Str ( "DynamicValue", ["bucket_size", Uint64;
                                                     "bucket_time", vigor_time_t;] )
(* TODO: make external_ip symbolic *)
module Iface : Fspec_api.Spec =
struct
(* FIXME: borrowed from ../nf/vigpolicer/policer_data_spec.ml *)
let containers = ["dyn_map", Map ("ip_addr", "capacity", "");
                  "dyn_keys", Vector ("ip_addr", "capacity", "");
                  "dyn_heap", DChain "capacity";
                  "dyn_vals", Vector ("DynamicValue", "capacity", "dyn_val_condition");
                  "capacity", UInt32;
                  "dev_count", UInt32;
                  "flow_emap", EMap ("ip_addr", "dyn_map", "dyn_keys", "dyn_heap");
                 ]

let records = String.Map.of_alist_exn
                ["ip_addr", ip_addr_struct;
                 "DynamicValue", dynamic_value_struct]
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

