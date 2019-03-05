open Core
open Str
open Fspec_api
open Ir
open Common_fspec

let flow_id_struct = Ir.Str ( "FlowId", ["src_port", Uint16;
                                         "dst_port", Uint16;
                                         "src_ip", Uint32;
                                         "dst_ip", Uint32;
                                         "internal_device", Uint16;
                                         "protocol", Uint8;] )

(* FIXME: borrowed from ../nf/vignat/nat_data_spec.ml *)
let containers = ["fm", Map ("FlowId", "max_flows", "");
                  "fv", Vector ("FlowId", "max_flows", "flow_consistency");
                  "heap", DChain "max_flows";
                  "max_flows", Int;
                  "start_port", Int;
                  "ext_ip", UInt32;
                  "nat_device", UInt32;
                  "", EMap ("FlowId", "fm", "fv", "heap")]

let records = String.Map.of_alist_exn
                ["FlowId", flow_id_struct]

let fun_types =
  String.Map.of_alist_exn
    (common_fun_types @
    [
     "map_allocate", (map_alloc_spec (gen_map_params containers records));
     "vector_allocate", (vector_alloc_spec (gen_vector_params containers records));
     "vector_borrow", (vector_borrow_spec (gen_vector_params containers records));
     "vector_return", (vector_return_spec (gen_vector_params containers records));
     "dchain_allocate", (dchain_alloc_spec (gen_dchain_params containers));
     "loop_invariant_consume", (loop_invariant_consume_spec containers);
     "loop_invariant_produce", (loop_invariant_produce_spec containers);
     "map_get", (map_get_spec (gen_map_params containers records));
     "map_put", (map_put_spec (gen_map_params containers records)) ;
     "expire_items_single_map", (expire_items_single_map_spec (gen_dchain_params containers));
     "dchain_allocate_new_index", (dchain_allocate_new_index_spec (gen_dchain_params containers));
     "dchain_rejuvenate_index", (dchain_rejuvenate_index_spec (gen_dchain_params containers));
     "dchain_is_index_allocated", dchain_is_index_allocated_spec;
    ])

(* TODO: make external_ip symbolic *)
module Iface : Fspec_api.Spec =
struct
  let preamble = gen_preamble "vignat/nat_loop.h" containers
  let fun_types = fun_types
  let boundary_fun = "loop_invariant_produce"
  let finishing_fun = "loop_invariant_consume"
  let eventproc_iteration_begin = "loop_invariant_produce"
  let eventproc_iteration_end = "loop_invariant_consume"
  let user_check_for_complete_iteration =
    (In_channel.read_all "forwarding_property.tmpl")
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

