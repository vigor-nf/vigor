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

let fun_types =
  String.Map.of_alist_exn
    (common_fun_types @
    [
     "map_allocate", (map_alloc_spec [("FlowIdi","FlowIdp","FlowId_eq","FlowId_hash","_FlowId_hash")]);
     "vector_allocate", (vector_alloc_spec [("FlowIdi", "FlowId", "FlowIdp", "FlowId_allocate", true)]);
     "vector_borrow", (vector_borrow_spec [("FlowIdi","FlowId","FlowIdp",noop,flow_id_struct,true)]);
     "vector_return", (vector_return_spec [("FlowIdi","FlowId","FlowIdp",flow_id_struct,true)]);
     "dchain_allocate", (dchain_alloc_spec [("65535",(Some "FlowIdi"))]);
     "loop_invariant_consume", (loop_invariant_consume_spec containers);
     "loop_invariant_produce", (loop_invariant_produce_spec containers);
     "map_get", (map_get_spec [("FlowIdi","FlowId","FlowIdp",(lma_literal_name "FlowId"),"last_flow_searched_in_the_map",flow_id_struct,noop,true)]);
     "map_put", (map_put_spec [("FlowIdi","FlowId","FlowIdp",(lma_literal_name "FlowId"),flow_id_struct,true)]) ;
     "expire_items_single_map", (expire_items_single_map_spec ["FlowIdi"]);
     "dchain_allocate_new_index", (dchain_allocate_new_index_spec (gen_dchain_map_related_specs containers));
     "dchain_rejuvenate_index", (dchain_rejuvenate_index_spec (gen_dchain_map_related_specs containers));
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

