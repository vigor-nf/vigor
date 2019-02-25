open Core
open Str
open Fspec_api
open Ir
open Common_fspec

type map_key = Int | Ext

let last_index_gotten = ref ""
let last_index_key = ref Int
let last_indexing_succ_ret_var = ref ""

let flow_id_struct = Ir.Str ( "FlowId", ["src_port", Uint16;
                                         "dst_port", Uint16;
                                         "src_ip", Uint32;
                                         "dst_ip", Uint32;
                                         "internal_device", Uint16;
                                         "protocol", Uint8;] )

let fun_types =
  String.Map.of_alist_exn
    (common_fun_types @
    [
     "map_allocate", (map_alloc_spec [("FlowIdi","FlowIdp","FlowId_eq","FlowId_hash","_FlowId_hash")]);
     "vector_allocate", (vector_alloc_spec [("FlowIdi", "FlowId", "FlowIdp", "FlowId_allocate", true)]);
     "vector_borrow", (vector_borrow_spec [("FlowIdi","FlowId","FlowIdp",noop,flow_id_struct,true)]);
     "vector_return", (vector_return_spec [("FlowIdi","FlowId","FlowIdp",flow_id_struct,true)]);
     "dchain_allocate", (dchain_alloc_spec "65535" (Some "FlowIdi"));
     "loop_invariant_consume", (loop_invariant_consume_spec [Ptr (Ptr map_struct);
                                                             Ptr (Ptr vector_struct);
                                                             Ptr (Ptr dchain_struct);
                                                             Sint32;
                                                             Sint32;
                                                             Uint32;
                                                             Uint32;
                                                             Uint32;
                                                             vigor_time_t]);
     "loop_invariant_produce", {ret_type = Static Void;
                                arg_types = stt [Ptr (Ptr map_struct);
                                                 Ptr (Ptr vector_struct);
                                                 Ptr (Ptr dchain_struct);
                                                 Sint32;
                                                 Sint32;
                                                 Uint32;
                                                 Uint32;
                                                 Ptr Uint32;
                                                 Ptr vigor_time_t];
                                extra_ptr_types = [];
                                lemmas_before = [];
                                lemmas_after = [
                                  (fun {args;_} ->
                                     "/*@ open evproc_loop_invariant (*" ^
                                     (List.nth_exn args 0) ^ ", *" ^
                                     (List.nth_exn args 1) ^ ", *" ^
                                     (List.nth_exn args 2) ^ ", " ^
                                     (List.nth_exn args 3) ^ ", " ^
                                     (List.nth_exn args 4) ^ ", " ^
                                     (List.nth_exn args 5) ^ ", " ^
                                     (List.nth_exn args 6) ^ ", *" ^
                                     (List.nth_exn args 7) ^ ", *" ^
                                     (List.nth_exn args 8) ^ "); @*/");
                                  (fun params ->
                                     "start_port = " ^ List.nth_exn params.args 4 ^ ";");
                                  (fun {args;_} ->
                                     "external_addr = " ^ List.nth_exn args 5 ^ ";");
                                  (fun {tmp_gen;args;_} ->
                                     "\n/*@ {\n\
                                      assert mapp<FlowIdi>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "fm") ^
                                     ", _));\n\
                                      assert map_vec_chain_coherent<FlowIdi>(" ^
                                     (tmp_gen "fm") ^ ", ?" ^
                                     (tmp_gen "fvk") ^ ", ?" ^
                                     (tmp_gen "ch") ^
                                     ");\n\
                                      mvc_coherent_same_len<FlowIdi>(" ^ 
                                     (tmp_gen "fm") ^
                                     ", " ^ (tmp_gen "fvk") ^
                                     ", " ^ (tmp_gen "ch") ^
                                     ");\n" ^
                                     "assert mapp<FlowIdi>(_ "^
                                     ", _, _, _, mapc(_, ?" ^ (tmp_gen "initial_flow_map") ^
                                     ", _));\n" ^
                                     "assert vectorp<FlowIdi>(_" ^
                                     ", _, ?" ^ (tmp_gen "initial_flow_vec") ^
                                     ", _);\n" ^
                                     "assert *" ^ (List.nth_exn args 2) ^ " |-> ?" ^ (tmp_gen "arg2bis") ^
                                     ";\nassert double_chainp(?" ^ (tmp_gen "initial_flow_chain") ^
                                     ", _);\n" ^
                                     "flow_chain = " ^ (tmp_gen "initial_flow_chain") ^ ";\n\
                                      flow_map = " ^ (tmp_gen "initial_flow_map") ^ ";\n\
                                      flow_vec = " ^ (tmp_gen "initial_flow_vec") ^ ";\n" ^
                                     "} @*/");
                                ];};
     "map_get", (map_get_spec [("FlowIdi","FlowId","FlowIdp",flow_id_struct,noop,true)]);
     "map_put", (map_put_spec [("FlowIdi","FlowId","FlowIdp",flow_id_struct,(fun str ->
         "FlowIdc(" ^ str ^
         "->src_port, " ^ str ^
         "->dst_port, " ^ str ^
         "->src_ip, " ^ str ^
         "->dst_ip, " ^ str ^
         "->internal_device, " ^ str ^
         "->protocol)"),true)]) ;
     "expire_items_single_map", (expire_items_single_map_spec ["FlowIdi"]);
     "dchain_allocate_new_index", (dchain_allocate_new_index_spec "FlowIdi");
     "dchain_rejuvenate_index", (dchain_rejuvenate_index_spec "FlowIdi");
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
                 "void to_verify()\n\
                  /*@ requires true; @*/ \n\
                  /*@ ensures true; @*/\n{\n\
                  int start_port;\n\
                  int external_addr;\n\
                  uint16_t received_on_port;\n\
                  int the_index_allocated = -1;\n\
                  int64_t time_for_allocated_index = 0;\n\
                  bool a_packet_received = false;\n\
                  //@ bool packet_is_complete = false;\n\
                  //@ option<void*> last_composed_packet = none;\n\
                  //@ list<uint8_t> last_sent_packet = nil;\n\
                  //@ dchain flow_chain;\n\
                  //@ list<pair<FlowIdi, int> > flow_map;\n\
                  //@ list<pair<FlowIdi, real> > flow_vec;\n\
                  //@ list<phdr> recv_headers = nil; \n\
                  //@ list<phdr> sent_headers = nil; \n\
                  //@ list<uint16_t> sent_on_ports = nil; \n\
                  //@ assume(sizeof(struct ether_hdr) == 14);\n\
                  //@ assume(sizeof(struct tcpudp_hdr) == 4);\n\
                  //@ assume(sizeof(struct ipv4_hdr) == 20);//TODO: handle all this sizeof's explicitly\n"
                 ^
                 "int vector_allocation_order = 0;\n\
                  int map_allocation_order = 0;\n\
                  int expire_items_single_map_order = 0;\n"
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

