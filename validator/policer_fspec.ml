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

let fun_types =
  String.Map.of_alist_exn
    (common_fun_types @
    ["loop_invariant_consume", (loop_invariant_consume_spec containers);
     "loop_invariant_produce", (loop_invariant_produce_spec containers);
     "dchain_allocate", (dchain_alloc_spec [("65536",(Some "ip_addri"))]);
     "dchain_allocate_new_index", (dchain_allocate_new_index_spec (gen_dchain_map_related_specs containers));
     "dchain_rejuvenate_index", (dchain_rejuvenate_index_spec (gen_dchain_map_related_specs containers));
     "expire_items_single_map", (expire_items_single_map_spec ["ip_addri"]);
     "map_allocate", (map_alloc_spec [("ip_addri","ip_addrp","ip_addr_eq","ip_addr_hash","_ip_addr_hash")]);
     "map_get", (map_get_spec [("ip_addri","ip_addr","ip_addrp",lma_literal_name "ip_addr","last_ip_addr_searched_in_the_map",ip_addr_struct,noop,true)]);
     "map_put", (map_put_spec [("ip_addri","ip_addr","ip_addrp",lma_literal_name "ip_addr",ip_addr_struct,true)]);
     "vector_allocate", (vector_alloc_spec [("ip_addri","ip_addr","ip_addrp","ip_addr_allocate",true);
                                            ("DynamicValuei","DynamicValue","DynamicValuep","DynamicValue_allocate",false);]);
     "vector_borrow",      (vector_borrow_spec [("ip_addri","ip_addr","ip_addrp",noop,ip_addr_struct,true);
                                                ("DynamicValuei","DynamicValue","DynamicValuep",noop,dynamic_value_struct,false);]);
     "vector_return",      (vector_return_spec [("ip_addri","ip_addr","ip_addrp",ip_addr_struct,true);
                                                ("DynamicValuei","DynamicValue","DynamicValuep",dynamic_value_struct,false);]);])

(* TODO: make external_ip symbolic *)
module Iface : Fspec_api.Spec =
struct
  let preamble = gen_preamble "vigpolicer/policer_loop.h" containers
  let fun_types = fun_types
  let boundary_fun = "loop_invariant_produce"
  let finishing_fun = "loop_invariant_consume"
  let eventproc_iteration_begin = "loop_invariant_produce"
  let eventproc_iteration_end = "loop_invariant_consume"
  let user_check_for_complete_iteration = In_channel.read_all "policer_forwarding_property.tmpl"
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

