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
                  "", EMap ("ether_addr", "dyn_map", "dyn_keys", "dyn_heap")]

let fun_types =
  String.Map.of_alist_exn
    (common_fun_types @
    [(hash_spec ether_addr_struct);
     "loop_invariant_consume", (loop_invariant_consume_spec containers);
     "loop_invariant_produce", (loop_invariant_produce_spec containers);
     "dchain_allocate", (dchain_alloc_spec (gen_dchain_specs containers));
     "dchain_allocate_new_index", (dchain_allocate_new_index_spec (gen_dchain_specs containers));
     "dchain_rejuvenate_index", (dchain_rejuvenate_index_spec (gen_dchain_specs containers));
     "expire_items_single_map", (expire_items_single_map_spec ["ether_addri"; "StaticKeyi"]);
     "map_allocate", (map_alloc_spec [
         {typ="ether_addr";coherent=true;entry_type=ether_addr_struct;open_callback=(fun name ->
              "//@ open [_]ether_addrp(" ^ name ^ ", _);\n")};
         {typ="StaticKey";coherent=false;entry_type=static_key_struct;open_callback=(fun name ->
              "//@ open StaticKeyp(" ^ name ^ ", _);\n" ^
              "//@ open ether_addrp(" ^ name ^ ".addr, _);\n")}]) ;
     "map_get", (map_get_spec [
         {typ="ether_addr";coherent=true;entry_type=ether_addr_struct;open_callback=(fun name ->
              "//@ open [_]ether_addrp(" ^ name ^ ", _);\n")};
         {typ="StaticKey";coherent=false;entry_type=static_key_struct;open_callback=(fun name ->
              "//@ open StaticKeyp(" ^ name ^ ", _);\n" ^
              "//@ open ether_addrp(" ^ name ^ ".addr, _);\n")}]);
     "map_put", (map_put_spec [
         {typ="ether_addr";coherent=true;entry_type=ether_addr_struct;open_callback=(fun name ->
              "//@ open [_]ether_addrp(" ^ name ^ ", _);\n")};
         {typ="StaticKey";coherent=false;entry_type=static_key_struct;open_callback=(fun name ->
              "//@ open StaticKeyp(" ^ name ^ ", _);\n" ^
              "//@ open ether_addrp(" ^ name ^ ".addr, _);\n")}]);
     "vector_allocate", (vector_alloc_spec [{typ="ether_addr";has_keeper=true;entry_type=ether_addr_struct;open_callback=(fun name ->
         "//@ open [_]ether_addrp(*" ^ name ^ ", _);\n")};
        {typ="DynamicValue";has_keeper=false;entry_type=dynamic_value_struct;open_callback=noop};
        {typ="StaticKey";has_keeper=true;entry_type=static_key_struct;open_callback=noop};]);
     "vector_borrow", (vector_borrow_spec [{typ="ether_addr";has_keeper=true;entry_type=ether_addr_struct;open_callback=(fun name ->
         "//@ open [_]ether_addrp(*" ^ name ^ ", _);\n")};
        {typ="DynamicValue";has_keeper=false;entry_type=dynamic_value_struct;open_callback=noop};
        {typ="StaticKey";has_keeper=true;entry_type=static_key_struct;open_callback=noop};]) ;
     "vector_return", (vector_return_spec [{typ="ether_addr";has_keeper=true;entry_type=ether_addr_struct;open_callback=(fun name ->
         "//@ open [_]ether_addrp(*" ^ name ^ ", _);\n")};
        {typ="DynamicValue";has_keeper=false;entry_type=dynamic_value_struct;open_callback=noop};
        {typ="StaticKey";has_keeper=true;entry_type=static_key_struct;open_callback=noop};]);])

(* TODO: make external_ip symbolic *)
module Iface : Fspec_api.Spec =
struct
  let preamble = gen_preamble "vigbridge/bridge_loop.h" containers
  let fun_types = fun_types
  let boundary_fun = "loop_invariant_produce"
  let finishing_fun = "loop_invariant_consume"
  let eventproc_iteration_begin = "loop_invariant_produce"
  let eventproc_iteration_end = "loop_invariant_consume"
  let user_check_for_complete_iteration = In_channel.read_all "bridge_forwarding_property.tmpl"
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

