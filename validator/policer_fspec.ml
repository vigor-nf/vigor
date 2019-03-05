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
     "dchain_allocate", (dchain_alloc_spec (gen_dchain_specs containers));
     "dchain_allocate_new_index", (dchain_allocate_new_index_spec (gen_dchain_specs containers));
     "dchain_rejuvenate_index", (dchain_rejuvenate_index_spec (gen_dchain_specs containers));
     "expire_items_single_map", (expire_items_single_map_spec ["ip_addri"]);
     "map_allocate", (map_alloc_spec [{typ="ip_addr";coherent=true;entry_type=ip_addr_struct;open_callback=noop}]);
     "map_get", (map_get_spec [{typ="ip_addr";coherent=true;entry_type=ip_addr_struct;open_callback=noop}]);
     "map_put", (map_put_spec [{typ="ip_addr";coherent=true;entry_type=ip_addr_struct;open_callback=noop}]);
     "vector_allocate", (vector_alloc_spec [{typ="ip_addr";has_keeper=true;entry_type=ip_addr_struct;open_callback=noop};
                                            {typ="DynamicValue";has_keeper=false;entry_type=dynamic_value_struct;open_callback=noop}]);
     "vector_borrow",      (vector_borrow_spec [{typ="ip_addr";has_keeper=true;entry_type=ip_addr_struct;open_callback=noop};
                                                {typ="DynamicValue";has_keeper=false;entry_type=dynamic_value_struct;open_callback=noop}]);
     "vector_return",      (vector_return_spec [{typ="ip_addr";has_keeper=true;entry_type=ip_addr_struct;open_callback=noop};
                                                {typ="DynamicValue";has_keeper=false;entry_type=dynamic_value_struct;open_callback=noop}]);])

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

