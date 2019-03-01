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
     "map_get", (map_get_spec [("FlowIdi","FlowId","FlowIdp","LMA_FLOW_ID","last_flow_searched_in_the_map",flow_id_struct,noop,true)]);
     "map_put", (map_put_spec [("FlowIdi","FlowId","FlowIdp","LMA_FLOW_ID",flow_id_struct,true)]) ;
     "expire_items_single_map", (expire_items_single_map_spec ["FlowIdi"]);
     "dchain_allocate_new_index", (dchain_allocate_new_index_spec ["FlowIdi","LMA_FLOW_ID"]);
     "dchain_rejuvenate_index", (dchain_rejuvenate_index_spec ["FlowIdi","LMA_FLOW_ID"]);
     "dchain_is_index_allocated", dchain_is_index_allocated_spec;
    ])

(* TODO: make external_ip symbolic *)
module Iface : Fspec_api.Spec =
struct
  let preamble = "\
#include \"lib/expirator.h\"\n\
#include \"lib/stubs/time_stub_control.h\"\n\
#include \"lib/containers/double-map.h\"\n\
#include \"lib/containers/double-chain.h\"\n\
#include \"lib/stubs/containers/double-map-stub-control.h\"\n\
#include \"vignat/nat_loop.h\"\n" ^
                 (In_channel.read_all "preamble.tmpl") ^
                 (In_channel.read_all "preamble_hide.tmpl") ^
                 "enum LMA_enum {LMA_FLOW_ID, LMA_INVALID};\n" ^
                 "void to_verify()\n\
                  /*@ requires true; @*/ \n\
                  /*@ ensures true; @*/\n{\n\
                  //@ int max_flows;\n\
                  //@ int start_port;\n\
                  //@ int ext_ip;\n\
                  //@ int nat_device;\n\
                  uint16_t received_on_port;\n\
                  int the_index_allocated = -1;\n\
                  int64_t time_for_allocated_index = 0;\n\
                  bool a_packet_received = false;\n\
                  //@ bool packet_is_complete = false;\n\
                  //@ option<void*> last_composed_packet = none;\n\
                  //@ list<uint8_t> last_sent_packet = nil;\n\
                  //@ dchain initial_heap;\n\
                  //@ list<pair<FlowIdi, int> > initial_fm;\n\
                  //@ list<pair<FlowIdi, real> > initial_fv;\n\
                  //@ list<phdr> recv_headers = nil; \n\
                  //@ list<phdr> sent_headers = nil; \n\
                  //@ list<uint16_t> sent_on_ports = nil; \n\
                  //@ assume(sizeof(struct ether_hdr) == 14);\n\
                  //@ assume(sizeof(struct tcpudp_hdr) == 4);\n\
                  //@ assume(sizeof(struct ipv4_hdr) == 20);//TODO: handle all this sizeof's explicitly\n"
                 ^ "//@ struct Map* fm_ptr;\n"
                 ^ "//@ struct DoubleChain* heap_ptr;\n"
                 ^ "//@ struct Vector* fv_ptr;\n"
                 ^
                 "int vector_allocation_order = 0;\n\
                  int map_allocation_order = 0;\n\
                  int dchain_allocation_order = 0;\n\
                  int expire_items_single_map_order = 0;\n\
                  enum LMA_enum last_map_accessed = LMA_FLOW_ID;\n\
                  FlowIdi last_flow_searched_in_the_map;\n"
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

