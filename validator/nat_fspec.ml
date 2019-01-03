open Core
open Str
open Fspec_api
open Ir

type map_key = Int | Ext

let last_index_gotten = ref ""
let last_index_key = ref Int
let last_indexing_succ_ret_var = ref ""
let last_time_for_index_alloc = ref ""


let gen_get_fp map_name =
  match !last_index_key with
  | Int-> "dmap_get_k1_fp(" ^ map_name ^ ", " ^ !last_index_gotten ^ ")"
  | Ext -> "dmap_get_k2_fp(" ^ map_name ^ ", " ^ !last_index_gotten ^ ")"

let capture_map map_name ptr_num {args;tmp_gen;_} =
  "//@ assert dmappingp<flow_id,flow_id,flow>(?" ^ (tmp_gen map_name) ^
  ",_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args ptr_num) ^ ");\n"

let capture_a_map t name {tmp_gen;_} =
  "//@ assert mapp<" ^ t ^ ">(_, _, _, _, mapc(_,?" ^ (tmp_gen name) ^ ", _));\n"

let capture_map_after map_name ptr_num (params:lemma_params) =
  "//@ assert dmappingp<flow_id,flow_id,flow>(?" ^ (params.tmp_gen map_name) ^
  ",_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn params.args ptr_num) ^ ");\n"

let capture_chain_after ch_name ptr_num (params:lemma_params) =
  "//@ assert double_chainp(?" ^ (params.tmp_gen ch_name) ^ ", " ^
  (List.nth_exn params.args ptr_num) ^ ");\n"

let capture_map_ex map_name vk1 vk2 ptr_num {args;tmp_gen;_} =
  "//@ assert dmappingp<flow_id,flow_id,flow>(?" ^ (tmp_gen map_name) ^
  ",_,_,_,_,_,_,_,_,?" ^ (tmp_gen vk1) ^ ",?" ^ (tmp_gen vk2) ^
  ",_,_," ^
  (List.nth_exn args ptr_num) ^ ");\n"

let capture_chain ch_name ptr_num {args;tmp_gen;_} =
  "//@ assert double_chainp(?" ^ (tmp_gen ch_name) ^ ", " ^
  (List.nth_exn args ptr_num) ^ ");\n"

let map_struct = Ir.Str ("Map", [])
let dmap_struct = Ir.Str ("Map", []) (*FIXME: delete this line*)
let vector_struct = Ir.Str ( "Vector", [] )
let dchain_struct = Ir.Str ( "DoubleChain", [] )
let flow_id_struct = Ir.Str ( "FlowId", ["src_port", Uint16;
                                         "dst_port", Uint16;
                                         "src_ip", Uint32;
                                         "dst_ip", Uint32;
                                         "protocol", Uint8;] )
let flow_struct = Ir.Str ("Flow", ["internal_id", flow_id_struct;
                                   "external_id", flow_id_struct;
                                   "internal_device", Uint16;])

let ether_addr_struct = Ir.Str ( "ether_addr", ["addr_bytes", Array (Uint8, 6);])
let ether_hdr_struct = Ir.Str ("ether_hdr", ["d_addr", ether_addr_struct;
                                             "s_addr", ether_addr_struct;
                                             "ether_type", Uint16;])
let ipv4_hdr_struct = Ir.Str ("ipv4_hdr", ["version_ihl", Uint8;
                                           "type_of_service", Uint8;
                                           "total_length", Uint16;
                                           "packet_id", Uint16;
                                           "fragment_offset", Uint16;
                                           "time_to_live", Uint8;
                                           "next_proto_id", Uint8;
                                            "hdr_checksum", Uint16;
                                           "src_addr", Uint32;
                                           "dst_addr", Uint32;])
let tcp_hdr_struct = Ir.Str ("tcp_hdr", ["src_port", Uint16;
                                         "dst_port", Uint16;
                                         "sent_seq", Uint32;
                                         "recv_ack", Uint32;
                                         "data_off", Uint8;
                                         "tcp_flags", Uint8;
                                         "rx_win", Uint16;
                                         "cksum", Uint16;
                                         "tcp_urp", Uint16;])

let stub_mbuf_content_struct = Ir.Str ( "stub_mbuf_content",
                                        ["ether", ether_hdr_struct;
                                         "ipv4", ipv4_hdr_struct;
                                         "tcp", tcp_hdr_struct;])

let rte_mempool_struct = Ir.Str ( "rte_mempool", [] )
let rte_mbuf_struct = Ir.Str ( "rte_mbuf",
                               ["buf_addr", Ptr stub_mbuf_content_struct;
                                "buf_iova", Uint64;
                                "data_off", Uint16;
                                "refcnt", Uint16;
                                "nb_segs", Uint16;
                                "port", Uint16;
                                "ol_flags", Uint64;
                                "packet_type", Uint32;
                                "pkt_len", Uint32;
                                "data_len", Uint16;
                                "vlan_tci", Uint16;
                                "hash", Uint32;
                                "vlan_tci_outer", Uint16;
                                "buf_len", Uint16;
                                "timestamp", Uint64;
                                "udata64", Uint64;
                                "pool", Ptr rte_mempool_struct;
                                "next", Ptr Void;
                                "tx_offload", Uint64;
                                "priv_size", Uint16;
                                "timesync", Uint16; 
                                "seqn", Uint32] )

(* VeriFast's C parser is quite limited, so simplify stuff... this is very brittle since it does no lookbehind to avoid accidents *)
let rec simplify_c_string str =
  let str0 = Str.global_replace (Str.regexp "\\*&") "" str in (* *&a  ==>  a *)
  let str0 = Str.global_replace (Str.regexp "\\*(&\\([^)]+\\))") "\\1" str0 in (* * (&a)  ==>  a *)
  let str0 = Str.global_replace (Str.regexp "&(\\([^)]+\\))->\\([^)]+\\)") "\\1.\\2" str0 in (* &a->b  ==>  a.b *)
  let str0 = Str.global_replace (Str.regexp "(&(\\([^)]+\\)))->\\([^)]+\\)") "\\1.\\2" str0 in (* (&a)->b  ==>  a.b *)
  let str0 = Str.global_replace (Str.regexp "(\\*\\([^)]+\\).\\([^)]+\\)") "\\1->\\2" str0 in (* ( *a ).b  ==>  a->b *)
  if str = str0 then str else simplify_c_string str0 (* find a fixpoint *)

let copy_stub_mbuf_content var_name ptr =
  ("struct stub_mbuf_content* tmp_smc_ptr" ^ var_name ^
   " = (" ^ ptr ^ ")->buf_addr;\n") ^
  deep_copy
    {Ir.name=var_name;
     Ir.value={v=Deref {v=Ir.Id ("tmp_smc_ptr" ^ var_name);
                        t=Ptr stub_mbuf_content_struct};
               t=stub_mbuf_content_struct}}

let fun_types =
  String.Map.of_alist_exn
    ["current_time", {ret_type = Static Sint64;
                      arg_types = [];
                      extra_ptr_types = [];
                      lemmas_before = [];
                      lemmas_after = [
                        (fun params ->
                        "time_t now = " ^ (params.ret_name) ^ ";\n")];};
     "start_time", {ret_type = Static Sint64;
                    arg_types = [];
                    extra_ptr_types = [];
                    lemmas_before = [];
                    lemmas_after = [];};
     "map_allocate", {ret_type = Static Sint32;
                      arg_types = stt [Fptr "map_keys_equality";
                                       Fptr "map_key_hash";
                                       Uint32;
                                       Ptr (Ptr map_struct)];
                      extra_ptr_types = [];
                      lemmas_before = [
                        (fun _ ->
                           "/*@ {\nproduce_function_pointer_chunk \
                            map_keys_equality<flow_id>(flow_id_eq)\
                            (flow_idp)(a, b) \
                            {\
                            call();\
                            }\n\
                            produce_function_pointer_chunk \
                            map_key_hash<flow_id>(flow_id_hash)\
                            (flow_idp, _flow_id_hash)(a) \
                            {\
                            call();\
                            }\n} @*/ \n");
                        ];
                      lemmas_after = [
                        ];};
     "vector_allocate", {ret_type = Static Sint32;
                         arg_types = stt [Sint32;
                                          Uint32;
                                          Fptr "vector_init_elem";
                                          Ptr (Ptr vector_struct)];
                         extra_ptr_types = [];
                         lemmas_before = [
                           tx_bl (* note that produce_function_pointer_chunk can only be done in an 'if', otherwise VeriFast complains *)
                              "if(!keys_v_allocated) {\n\
                                produce_function_pointer_chunk vector_init_elem<flow_id>(flow_id_allocate)\
                                (flow_idp, sizeof(struct FlowId))(a) \
                                {\
                                call();\
                                }\n\
                               } else {\n\
                                produce_function_pointer_chunk vector_init_elem<flow>(flow_allocate)\
                                (flowp, sizeof(struct Flow))(a) \
                                {\
                                call();\
                                }\n\
                              }\n";
                           (fun {args;_} ->
                              "/*@ if (!keys_v_allocated) { \n\
                               assume(sizeof(struct FlowId) == " ^
                              (List.nth_exn args 0) ^
                              ");\n } else { \n\
                               assume(sizeof(struct Flow) == " ^
                              (List.nth_exn args 0) ^ ");\n} @*/ ");
                         ];
                         lemmas_after = [
                           (fun {tmp_gen;ret_name;_} ->
                              "/*@ if (" ^ ret_name ^
                              ") {\n\
                               if (!keys_v_allocated) {\n\
                               assert mapp<flow_id>(_, _, _, _, mapc(?" ^ (tmp_gen "cap") ^
                              ", ?" ^ (tmp_gen "map") ^
                              ", ?" ^ (tmp_gen "addr_map") ^
                              "));\n\
                               assert vectorp<flow_id>(_, _, ?" ^ (tmp_gen "dks") ^
                              ", ?" ^ (tmp_gen "dkaddrs") ^
                              ");\n\
                               empty_kkeeper(" ^
                              (tmp_gen "dkaddrs") ^
                              ", " ^ (tmp_gen "dks") ^
                              ", " ^ (tmp_gen "addr_map") ^
                              ", " ^ (tmp_gen "cap") ^
                              ");\n\
                               } \n\
                               }@*/");
                           (fun {args;_} ->
                              "if (!keys_v_allocated) {\n\
                               keys_v_allocated = true; }");];};
     "vector_borrow",      {ret_type = Static Void;
                            arg_types = [Static (Ptr vector_struct);
                                         Static Sint32;
                                         Dynamic ["FlowId", Ptr (Ptr flow_id_struct);
                                                  "Flow", Ptr (Ptr flow_struct)];];
                            extra_ptr_types = ["borrowed_cell",
                                               Dynamic ["FlowId", Ptr flow_id_struct;
                                                        "Flow", Ptr flow_struct];];
                            lemmas_before = [
                              (fun params ->
                                 match List.nth_exn params.arg_types 2 with
                                 | Ptr (Ptr (Str ("FlowId", _))) ->
                                   "/*@ if (!values_v_borrowed) { close hide_vector<flow>(_, _, _, _); } @*/\n" ^
                                   "//@ assert vectorp<flow_id>(" ^ (List.nth_exn params.args 0) ^
                                   ", flow_idp, ?" ^ (params.tmp_gen "vec") ^ ", ?" ^ (params.tmp_gen "veca") ^
                                   ");\n//@ vector_addrs_same_len_nodups(" ^ (List.nth_exn params.args 0) ^ ");\n"
                                 | Ptr (Ptr (Str ("Flow", _))) ->
                                   "/*@ if (!keys_v_borrowed) { close hide_vector<flow_id>(_, _, _, _); } @*/\n" ^
                                   "/*@ { assert vectorp<flow>(_, _, ?" ^ (params.tmp_gen "vec") ^ ", _);\n\
                                          forall_mem(nth(" ^ (List.nth_exn params.args 1) ^ ", " ^ (params.tmp_gen "vec") ^ "), " ^ (params.tmp_gen "vec") ^ ", is_one);\n } @*/\n"
                                 | _ ->
                                   failwith "Unsupported type for vector!")
                            ];
                            lemmas_after = [
                              (fun params ->
                                 match List.nth_exn params.arg_types 2 with
                                 | Ptr (Ptr (Str ("FlowId", _))) ->
                                   "/*@ if (!values_v_borrowed) { open hide_vector<flow>(_, _, _, _); } @*/\n" ^
                                   "keys_v_borrowed = true;\n" ^
                                   "struct FlowId * " ^ (params.tmp_gen "elem") ^
                                   " = *" ^ (List.nth_exn params.args 2) ^ ";\n" ^
                                   "//@ assert [?" ^ (params.tmp_gen "fr") ^
                                   "]flow_idp(" ^ (params.tmp_gen "elem") ^ ", _);\n" ^
                                   "/*@ if (" ^ (params.tmp_gen "fr") ^
                                   " != 1.0) {\n\
                                    assert mapp<flow_id>(_, _, _, _, mapc(_,?" ^ (params.tmp_gen "fm") ^
                                   ", ?" ^ (params.tmp_gen "fma") ^
                                   "));\n\
                                    forall2_nth(" ^ (params.tmp_gen "vec") ^ ", " ^ (params.tmp_gen "veca") ^
                                   ", (kkeeper)(" ^ (params.tmp_gen "fma") ^ "), " ^ (List.nth_exn params.args 1) ^
                                   ");\n} @*/ "
                                 | Ptr (Ptr (Str ("Flow", _))) ->
                                   "/*@ if (!keys_v_borrowed) { open hide_vector<flow_id>(_, _, _, _); } @*/\n" ^
                                   "values_v_borrowed = true; \n"
                                 | _ ->
                                   failwith "Unsupported type for vector!")
                            ];};
     "vector_return",      {ret_type = Static Void;
                            arg_types = [Static (Ptr vector_struct);
                                         Static Sint32;
                                         Dynamic ["FlowId", Ptr flow_id_struct;
                                                  "Flow", Ptr flow_struct];];
                            extra_ptr_types = [];
                            lemmas_before = [
                              (fun params ->
                                 match List.nth_exn params.arg_types 2 with
                                 | Ptr (Str ("FlowId", _)) ->
                                   "/*@ { assert vector_accp<flow_id>(_, _, ?" ^ (params.tmp_gen "vec") ^ ", _, _, _); \n\
                                          update_id(" ^ (List.nth_exn params.args 1) ^ ", " ^ (params.tmp_gen "vec") ^ "); } @*/"
                                 | Ptr (Str ("Flow", _)) ->
                                   "/*@ { assert vector_accp<flow>(_, _, ?" ^ (params.tmp_gen "vec") ^
                                   ", _, _, _); \n\
                                    assert *&" ^
                                   (Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn params.args 2)) ^
                                   " |-> ? " ^ (params.tmp_gen "flw") ^
                                   ";\n\
                                    assert flowp(" ^
                                   (params.tmp_gen "flw") ^
                                   ", ?" ^ (params.tmp_gen "flw_logical") ^
                                   ");\n\
                                    forall_update<pair<flow, real> >(" ^ (params.tmp_gen "vec") ^
                                   ", is_one, " ^ (List.nth_exn params.args 1) ^
                                   ", pair(" ^ (params.tmp_gen "flw_logical") ^
                                   ", 1.0));\n\
                                    update_id(" ^ (List.nth_exn params.args 1) ^ ", " ^ (params.tmp_gen "vec") ^ "); } @*/"
                                 | _ ->
                                   failwith "Unsupported type for vector!");
                              (fun params ->
                                 match List.nth_exn params.arg_types 2 with
                                 | Ptr (Str ("FlowId", _)) ->
                                   "/*@ if (values_v_borrowed) { close hide_vector_acc<flow>(_, _, _, _, _, _); } @*/\n"
                                 | Ptr (Str ("Flow", _)) ->
                                   "/*@ if (keys_v_borrowed) { close hide_vector_acc<flow_id>(_, _, _, _, _, _); } @*/\n"
                                 | _ ->
                                   failwith "Unsupported type for vector!")
                            ];
                            lemmas_after = [
                              (fun params ->
                                 match List.nth_exn params.arg_types 2 with
                                 | Ptr (Str ("FlowId", _)) ->
                                   "/*@ if (values_v_borrowed) { open hide_vector_acc<flow>(_, _, _, _, _, _); } @*/\n" ^
                                   "keys_v_borrowed = false;"
                                 | Ptr (Str ("Flow", _)) ->
                                   "/*@ if (keys_v_borrowed) { open hide_vector_acc<flow_id>(_, _, _, _, _, _); } @*/\n" ^
                                   "values_v_borrowed = false;"
                                 | _ ->
                                   failwith "Unsupported type for vector!")
                            ];};
     "dchain_allocate", {ret_type = Static Sint32;
                         arg_types = stt [Sint32; Ptr (Ptr dchain_struct)];
                         extra_ptr_types = [];
                         lemmas_before = [];
                         lemmas_after = [
                           on_rez_nonzero
                             "{\n\
                              assert vectorp<flow_id>(_, _, ?allocated_vector, _);\n\
                              empty_map_vec_dchain_coherent\
                              <flow_id>(allocated_vector);\n}";
                           tx_l "index_range_of_empty(65536, 0);";];};
     "loop_invariant_consume", {ret_type = Static Void;
                                arg_types = stt [Ptr (Ptr map_struct);
                                                 Ptr (Ptr vector_struct);
                                                 Ptr (Ptr dchain_struct);
                                                 Ptr (Ptr vector_struct);
                                                 Uint32;
                                                 Sint64;
                                                 Sint32;
                                                 Sint32];
                                extra_ptr_types = [];
                                lemmas_before = [
                                  (fun {args;_} ->
                                     "start_port = " ^ List.nth_exn args 7 ^ ";");
                                  (fun {args;_} ->
                                     "/*@ close evproc_loop_invariant(*" ^
                                     List.nth_exn args 0 ^ ", *" ^
                                     List.nth_exn args 1 ^ ", *" ^
                                     List.nth_exn args 2 ^ ", *" ^
                                     List.nth_exn args 3 ^ ", " ^
                                     List.nth_exn args 4 ^ ", " ^
                                     List.nth_exn args 5 ^ ", " ^
                                     List.nth_exn args 6 ^ ", " ^
                                     List.nth_exn args 7 ^ "); @*/");
                                ];
                                lemmas_after = [];};
     "loop_invariant_produce", {ret_type = Static Void;
                                arg_types = stt [Ptr (Ptr map_struct);
                                                 Ptr (Ptr vector_struct);
                                                 Ptr (Ptr dchain_struct);
                                                 Ptr (Ptr vector_struct);
                                                 Ptr Uint32;
                                                 Ptr Sint64;
                                                 Sint32;
                                                 Sint32];
                                extra_ptr_types = [];
                                lemmas_before = [];
                                lemmas_after = [
                                  (fun {args;_} ->
                                     "/*@ open evproc_loop_invariant (*" ^
                                     (List.nth_exn args 0) ^ ", *" ^
                                     (List.nth_exn args 1) ^ ", *" ^
                                     (List.nth_exn args 2) ^ ", *" ^
                                     (List.nth_exn args 3) ^ ", *" ^
                                     (List.nth_exn args 4) ^ ", *" ^
                                     (List.nth_exn args 5) ^ ", " ^
                                     (List.nth_exn args 6) ^ ", " ^
                                     (List.nth_exn args 7) ^ "); @*/");
                                  (fun params ->
                                     "start_port = " ^ List.nth_exn params.args 7 ^ ";");
                                  (fun {tmp_gen;args;_} ->
                                     "\n/*@ {\n\
                                      assert mapp<flow_id>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "fm") ^
                                     ", _));\n\
                                      assert vectorp<flow_id>(_, _, ?" ^ (tmp_gen "fvk") ^
                                     ", _);\n\
                                      assert vectorp<flow>(_, _, ?" ^ (tmp_gen "fvv") ^
                                     ", _);\n\
                                      assert map_vec_chain_coherent<flow_id>(" ^
                                     (tmp_gen "fm") ^ ", " ^
                                     (tmp_gen "fvk") ^ ", ?" ^
                                     (tmp_gen "ch") ^
                                     ");\n\
                                      mvc_coherent_same_len<flow_id>(" ^ 
                                     (tmp_gen "fm") ^
                                     ", " ^ (tmp_gen "fvk") ^
                                     ", " ^ (tmp_gen "ch") ^
                                     ");\n" ^ (*TODO: capture initial_* values*)
                                     "} @*/");
                                ];};
     "dmap_get_b", {ret_type = Static Sint32;
                    arg_types = stt [Ptr dmap_struct; Ptr flow_id_struct; Ptr Sint32;];
                    extra_ptr_types = [];
                    lemmas_before = [
                      capture_map "cur_map" 0;
                      (fun {args;_} ->
                         "/*@ close flow_idp(" ^ List.nth_exn args 1 ^
                         ", ?ext_key_dgb); @*/"); ];
                    lemmas_after = [
                      (fun params ->
                         "/*@ {\n assert dmap_dchain_coherent(" ^
                         (params.tmp_gen "cur_map") ^
                         ", ?cur_ch);\n\
                          contains_flow_id_ext_abstract(" ^
                         (params.tmp_gen "cur_map") ^
                         ", cur_ch,\n ext_key_dgb);\n}@*/");
                      on_rez_nz
                        (fun params ->
                           "{\n dmap_get_k2_limits(" ^
                           (params.tmp_gen "cur_map") ^
                           ", ext_key_dgb);\n}");
                      on_rez_nz
                        (fun params ->
                           "{\n dmap_get_k2_get_val(" ^
                           (params.tmp_gen "cur_map") ^
                           ", ext_key_dgb);\n}");
                      on_rez_nz
                        (fun params ->
                           "{\n assert dmap_dchain_coherent(" ^
                           (params.tmp_gen "cur_map") ^
                           ", ?cur_ch);\n" ^
                           "flow_id ek = ext_key_dgb;\n"^
                           "get_flow_by_ext_abstract(" ^
                           (params.tmp_gen "cur_map") ^ ", cur_ch, ek);\n" ^
                           "coherent_dmap_used_dchain_allocated(" ^
                           (params.tmp_gen "cur_map") ^ ", cur_ch, dmap_get_k2_fp(" ^
                           (params.tmp_gen "cur_map") ^ ", ek));\n}");
                      (fun params ->
                         last_index_gotten :=
                           "ext_key_dgb";
                         last_index_key := Ext;
                         last_indexing_succ_ret_var := params.ret_name;
                         "");
                    ];};
     "map_get", {ret_type = Static Sint32;
                 arg_types = stt [Ptr map_struct;
                                  Ptr flow_id_struct;
                                  Ptr Sint32];
                 extra_ptr_types = [];
                 lemmas_before = [
                   (fun ({arg_exps;tmp_gen;_} as params) ->
                        "//@ assert flow_idp(" ^ (render_tterm (List.nth_exn arg_exps 1)) ^
                        ", ?" ^ (tmp_gen "fk") ^ ");\n" ^
                         capture_a_map "flow_id" "dm" params ^
                         "//@ assert map_vec_chain_coherent<flow_id>(" ^
                         (tmp_gen "dm") ^ ", ?" ^
                         (tmp_gen "dv") ^ ", ?" ^
                         (tmp_gen "dh") ^ ");\n"
                      );];
                 lemmas_after = [
                   (fun {ret_name;tmp_gen;args;_} ->
                        "/*@ if (" ^ ret_name ^
                        " != 0) {\n\
                         mvc_coherent_map_get_bounded(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ", " ^
                        (tmp_gen "fk") ^
                        ");\n\
                         mvc_coherent_map_get_vec_half(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ", " ^
                        (tmp_gen "fk") ^
                        ");\n\
                         mvc_coherent_map_get(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ", " ^
                        (tmp_gen "fk") ^ ");\n} @*/"
                      );
                   ];};
     "dmap_get_a", {ret_type = Static Sint32;
                    arg_types = stt [Ptr dmap_struct; Ptr flow_id_struct; Ptr Sint32;];
                    extra_ptr_types = [];
                    lemmas_before = [
                      capture_map "cur_map" 0;
                      (fun params -> "//@ close flow_idp(" ^ (List.nth_exn params.args 1) ^ ", ?int_key_dga);")];
                    lemmas_after = [
                      (fun params ->
                         "/*@ {\n assert dmap_dchain_coherent(" ^
                         (params.tmp_gen "cur_map") ^
                         ", ?cur_ch);\n\
                          contains_flow_id_int_abstract(" ^
                         (params.tmp_gen "cur_map") ^
                         ", cur_ch,\n int_key_dga);\n}@*/");
                      on_rez_nz
                        (fun params ->
                           "{\n dmap_get_k1_limits(" ^
                           (params.tmp_gen "cur_map") ^
                           ", int_key_dga);\n}");
                      on_rez_nz
                        (fun params ->
                           "{\n dmap_get_k1_get_val(" ^
                           (params.tmp_gen "cur_map") ^
                           ", int_key_dga);\n}");
                      on_rez_nz
                        (fun params ->
                           "{\n" ^
                           "flow_id ik = int_key_dga;\n" ^
                           " assert dmap_dchain_coherent(" ^
                           (params.tmp_gen "cur_map") ^ ", ?cur_ch);\n" ^
                           "get_flow_by_int_abstract(" ^
                           (params.tmp_gen "cur_map") ^ ", cur_ch, ik);\n" ^
                           "coherent_dmap_used_dchain_allocated(" ^
                           (params.tmp_gen "cur_map") ^
                           ", cur_ch, dmap_get_k1_fp(" ^
                           (params.tmp_gen "cur_map") ^
                           ", ik));\n}");
                      (fun params ->
                         last_index_gotten :=
                           "int_key_dga";
                         last_index_key := Int;
                         last_indexing_succ_ret_var := params.ret_name;
                         "");
                    ];};
     "map_put", {ret_type = Static Void;
                 arg_types = stt [Ptr map_struct;
                                  Ptr flow_id_struct;
                                  Sint32];
                 extra_ptr_types = [];
                 lemmas_before = [
                   (fun {args;tmp_gen;_} ->
                        "\n//@ assert mapp<flow_id>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "dm") ^
                        ", _));\n" ^
                        "\n/*@ {\n\
                         assert map_vec_chain_coherent<flow_id>(" ^
                        (tmp_gen "dm") ^ ", ?" ^
                        (tmp_gen "dv") ^ ", ?" ^
                        (tmp_gen "dh") ^
                        ");\n\
                         mvc_coherent_dchain_non_out_of_space_map_nonfull<flow_id>(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ");\n" ^
                         "mvc_coherent_bounds<flow_id>(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ");\n} @*/\n" ^
                        let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
                        "/*@ { \n\
                         assert mapp<flow_id>(_, _, _, _, mapc(_, _, ?dm_addrs)); \n\
                         assert vector_accp<flow_id>(_, _, ?the_dv, ?dv_addrs, _, _); \n\
                         assert map_vec_chain_coherent<flow_id>(?the_dm, the_dv, ?the_dh);\n\
                         flow_id vvv = flid(" ^ arg1 ^
                        "->src_port, " ^ arg1 ^
                        "->dst_port, " ^ arg1 ^
                        "->src_ip, " ^ arg1 ^
                        "->dst_ip, " ^ arg1 ^
                        "->protocol); \n\
                         mvc_coherent_key_abscent(the_dm, the_dv, the_dh, vvv);\n\
                         kkeeper_add_one(dv_addrs, the_dv, dm_addrs, vvv, " ^ (List.nth_exn args 2) ^
                        "); \n\
                         } @*/\n"
                      );];
                 lemmas_after = [
                   (fun {args;tmp_gen;_} ->
                        let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
                        "\n/*@ {\n\
                         assert map_vec_chain_coherent<flow_id>(" ^ (tmp_gen "dm") ^
                        ", ?" ^ (tmp_gen "dv") ^
                        ", ?" ^ (tmp_gen "dh") ^
                        ");\n\
                         flow_id " ^ (tmp_gen "ea") ^ " = flw(" ^ arg1 ^
                        "->src_port, " ^ arg1 ^
                        "->dst_port, " ^ arg1 ^
                        "->src_ip, " ^ arg1 ^
                        "->dst_ip, " ^ arg1 ^
                        "->protocol);\n\
                         mvc_coherent_put<flow_id>(" ^ (tmp_gen "dm") ^
                        ", " ^ (tmp_gen "dv") ^
                        ", " ^ (tmp_gen "dh") ^
                        ", " ^ (List.nth_exn args 2) ^
                        ", time_for_allocated_index, " ^ (tmp_gen "ea") ^
                        ");\n\
                         } @*/\n"
                      );];};
     "dmap_put", {ret_type = Static Sint32;
                  arg_types = stt [Ptr dmap_struct; Ptr flow_struct; Sint32;];
                  extra_ptr_types = [];
                  lemmas_before = [
                    capture_map_ex "cur_map" "vk1" "vk2" 0;
                    (fun {args;tmp_gen;_} ->
                       "/*@ flow the_inserted_flow; @*/\n\
                        /*@ {\n" ^
                       "close flow_idp(" ^ (List.nth_exn args 1) ^
                    ".internal_id, flid(?isp, ?dp, ?isip, ?dip, user_buf_23));\n" ^
                     "assert flow_idp(" ^ (List.nth_exn args 1) ^
                     ".internal_id, flid(?isp, ?dp, ?isip, ?dip, user_buf_23));\n" ^
                     "close flow_idp(" ^ (List.nth_exn args 1) ^
                    ".external_id, flid(dp, new_index_2_0, dip, external_ip, user_buf_23));\n" ^
                    " close flowp(" ^ (List.nth_exn args 1) ^
                    ", flw(flid(isp, dp, isip, dip, user_buf_23),\
                           flid(dp, new_index_2_0, dip, external_ip, user_buf_23), received_on_port));\n" ^
                       "assert dmap_dchain_coherent(" ^
                         (tmp_gen "cur_map") ^
                       ", ?cur_ch);\n\
                        flow_id ek = flid(dp, new_index_2_0, dip,\
                        external_ip, user_buf_23);\n\
                        if (dmap_has_k2_fp(" ^ (tmp_gen "cur_map") ^
                       ", ek)) {\n\
                        int index = dmap_get_k2_fp(" ^ (tmp_gen "cur_map") ^
                       ", ek);\n\
                        dmap_get_k2_limits(" ^ (tmp_gen "cur_map") ^
                       ", ek);\n\
                        flow value = dmap_get_val_fp(" ^ (tmp_gen "cur_map") ^
                       ", index);\n\
                        dmap_get_by_index_rp(" ^ (tmp_gen "cur_map") ^
                       ", index);\n\
                        dmap_get_by_k2_invertible(" ^ (tmp_gen "cur_map") ^
                       ", ek);\n\
                        assert(index == " ^ (List.nth_exn args 2) ^ ");\n\
                        assert(true == dmap_index_used_fp(" ^ (tmp_gen "cur_map") ^
                       ", " ^ (List.nth_exn args 2) ^ "));\n\
                        coherent_dmap_used_dchain_allocated(" ^ (tmp_gen "cur_map") ^
                       ", cur_ch, " ^ (List.nth_exn args 2) ^ ");\n\
                        assert(true == dchain_allocated_index_fp(" ^
                       (tmp_gen "cur_map") ^
                       ", " ^ (List.nth_exn args 2) ^ "));\n\
                        assert(false);\n\
                        }\n\
                        assert dmap_dchain_coherent(" ^ (tmp_gen "cur_map") ^
                       ", cur_ch);\n\
                        if (dmap_index_used_fp(" ^ (tmp_gen "cur_map") ^
                       ", " ^ (List.nth_exn args 2) ^ ")) {\n\
                        coherent_dmap_used_dchain_allocated(" ^ (tmp_gen "cur_map") ^
                       ", cur_ch, " ^ (List.nth_exn args 2) ^ ");\n\
                        }\n\
                        dmap_put_preserves_cap(" ^ (tmp_gen "cur_map") ^
                       ", " ^ (List.nth_exn args 2) ^ ", flw(flid(isp, dp,\
                        isip, dip, user_buf_23),\n\
                        flid(dp, new_index_2_0, dip, external_ip, user_buf_23), received_on_port)," ^
                       (tmp_gen "vk1") ^ ", " ^ (tmp_gen "vk2") ^ ");\n" ^
                       "the_inserted_flow = " ^
                       " flw(flid(isp, dp,\
                        isip, dip, user_buf_23),\n\
                        flid(dp, new_index_2_0, dip, external_ip, user_buf_23), received_on_port);\n\
                       assert dmap_dchain_coherent(" ^ (tmp_gen "cur_map") ^
                      ", ?ch);\n\
                       flow_id ik = flid(isp, dp,\
                        isip, dip, user_buf_23);\n\
                       coherent_dchain_non_out_of_space_map_nonfull(" ^
                      (tmp_gen "cur_map") ^ ", ch);\n" ^
                      "contains_flow_id_ext_abstract(" ^
                      (tmp_gen "cur_map") ^
                      ", ch, ek);\n" ^
                      "flow the_flow_to_insert = flw(ik, ek, received_on_port);\n" ^
                       "add_flow_abstract(" ^ (tmp_gen "cur_map") ^
                       ", ch, the_flow_to_insert, " ^
                       (List.nth_exn args 2) ^ ", " ^
                       !last_time_for_index_alloc ^ ");\n} @*/");];
                  lemmas_after = [
                    (fun params ->
                       "/*@ {\n\
                        close flowp(" ^ (List.nth_exn params.args 1) ^
                       ", ?flw);\n\
                         open flowp(_, flw);\n\
                         open flow_idp(_,?ik);\n\
                         open flow_idp(_,?ek);\n\
                        if (" ^ params.ret_name ^
                       "!= 0) {\n\
                        dmap_put_get(" ^
                       (params.tmp_gen "cur_map") ^
                       "," ^ (List.nth_exn params.args 2) ^ ",\
                        flw,\n" ^
                       (params.tmp_gen "vk1") ^ ", " ^
                       (params.tmp_gen "vk2") ^ ");\n}\n\
                       if (" ^ params.ret_name ^
                       "!= 0) {\n\
                        assert dmap_dchain_coherent(" ^
                       (params.tmp_gen "cur_map") ^
                       ", ?cur_ch);\n\
                        flow the_flow_to_insert = flw;\n" ^
                      "coherent_put_allocated_preserves_coherent\n(" ^
                      (params.tmp_gen "cur_map") ^
                      ", cur_ch, ik , ek,\
                       the_flow_to_insert,\
                      " ^ (List.nth_exn params.args 2) ^ ", " ^
                      !last_time_for_index_alloc ^
                      ", " ^ (params.tmp_gen "vk1") ^ ", " ^
                      (params.tmp_gen "vk2") ^ ");\n}\n\
                                                } @*/");
                  ];};
     "dmap_get_value", {ret_type = Static Void;
                        arg_types = stt [Ptr dmap_struct; Sint32; Ptr flow_struct;];
                        extra_ptr_types = [];
                        lemmas_before = [
                          capture_map "cur_map" 0;
                          (fun {tmp_gen;_} ->
                             "/*@ {\
                              assert dmap_dchain_coherent(" ^ (tmp_gen "cur_map") ^
                             ", ?cur_ch);\n\
                              coherent_same_cap(" ^ (tmp_gen "cur_map") ^
                             ", cur_ch);\n\
                              }@*/");
                          (fun {args;_} ->
                             "//@ open_struct(" ^
                             (List.nth_exn args 2) ^ ");")];
                        lemmas_after = [
                          (fun params ->
                             "/*@{ if (" ^ !last_indexing_succ_ret_var ^
                             "!= 0) { \n\
                              assert dmap_dchain_coherent(" ^
                             (params.tmp_gen "cur_map") ^
                             ", ?cur_ch);\n\
                              coherent_dmap_used_dchain_allocated(" ^
                             (params.tmp_gen "cur_map") ^ ", cur_ch," ^
                             (gen_get_fp (params.tmp_gen "cur_map")) ^
                             "); }} @*/\n");
                          (fun params ->
                             "/*@\
                              open flowp(" ^ (List.nth_exn params.args 2) ^
                             ", _);\n\
                              @*/");
                          tx_l "open flow_idp(_,_);";
                          tx_l "open flow_idp(_,_);";
                        ];};
     "expire_items_single_map", {ret_type = Static Sint32;
                                 arg_types = stt [Ptr dchain_struct;
                                                  Ptr vector_struct;
                                                  Ptr map_struct;
                                                  time_t];
                                 extra_ptr_types = [];
                                 lemmas_before = [
                                   (fun {tmp_gen;args;_} ->
                                      "//@ assert double_chainp(?" ^
                                      (tmp_gen "cur_ch") ^ ", " ^ (List.nth_exn args 0) ^ ");\n" ^
                                      "//@ expire_olds_keeps_high_bounded(" ^
                                      (tmp_gen "cur_ch") ^ ", " ^ (List.nth_exn args 3) ^ ");\n");
                                   (fun {args;tmp_gen;_} ->
                                      "/*@ {\n\
                                       expire_preserves_index_range(" ^
                                      (tmp_gen "cur_ch") ^ ", " ^
                                      (List.nth_exn args 3) ^
                                      ");\n\
                                       length_nonnegative(\
                                       dchain_get_expired_indexes_fp(" ^
                                      (tmp_gen "cur_ch") ^ ", " ^
                                      (List.nth_exn args 3) ^
                                      "));\n\
                                       if (length(dchain_get_expired_indexes_fp(" ^
                                      (tmp_gen "cur_ch") ^ ", " ^
                                      (List.nth_exn args 3) ^
                                      ")) > 0 ) {\n\
                                       expire_old_dchain_nonfull\
                                       (" ^ (List.nth_exn args 0) ^ ", " ^
                                      (tmp_gen "cur_ch") ^ ", " ^
                                      (List.nth_exn args 3) ^
                                      ");\n\
                                       }} @*/");
                                 ];
                                 lemmas_after = [
                                   (fun {tmp_gen;_} ->
                                      "/*@ {\n\
                                       assert mapp<flow_id>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "fm") ^ ", _));\n\
                                       assert vectorp<flow_id>(_, _, ?" ^ (tmp_gen "fvk") ^ ", _);\n\
                                       assert map_vec_chain_coherent<flow_id>(" ^
                                      (tmp_gen "fm") ^ ", " ^
                                      (tmp_gen "fvk") ^ ", ?" ^
                                      (tmp_gen "ch") ^
                                      ");\n\
                                      mvc_coherent_same_len<flow_id>(" ^
                                      (tmp_gen "fm") ^ ", " ^
                                      (tmp_gen "fvk") ^ ", " ^
                                      (tmp_gen "ch") ^ ");\n} @*/");
                                 ];};
     "expire_items", {ret_type = Static Sint32;
                      arg_types = stt [Ptr dchain_struct;
                                       Ptr dmap_struct;
                                       time_t];
                      extra_ptr_types = [];
                      lemmas_before = [
                        capture_chain "cur_ch" 0;
                        capture_map_ex "cur_map" "vk1" "vk2" 1;
                        (fun {args;tmp_gen;_} ->
                           "//@ expire_flows_abstract(" ^ (tmp_gen "cur_map") ^
                           ", " ^ (tmp_gen "cur_ch") ^
                           ", " ^ (List.nth_exn args 2) ^ ");");
                        (fun {args;tmp_gen;_} ->
                           "/*@ {\n\
                            expire_preserves_index_range(" ^
                           (tmp_gen "cur_ch") ^ ", " ^
                           (List.nth_exn args 2) ^
                           ");\n\
                           length_nonnegative(\
                            dchain_get_expired_indexes_fp(" ^
                           (tmp_gen "cur_ch") ^ ", " ^
                           (List.nth_exn args 2) ^
                           "));\n\
                            if (length(dchain_get_expired_indexes_fp(" ^
                           (tmp_gen "cur_ch") ^ ", " ^
                           (List.nth_exn args 2) ^
                           ")) > 0 ) {\n\
                            expire_old_dchain_nonfull\
                            (" ^ (List.nth_exn args 0) ^ ", " ^
                           (tmp_gen "cur_ch") ^ ", " ^
                           (List.nth_exn args 2) ^
                           ");\n\
                            }} @*/");
                        (fun {args;tmp_gen;_} ->
                           "/*@ dmap_erase_all_preserves_cap(" ^
                           (tmp_gen "cur_map") ^ ", " ^
                           "dchain_get_expired_indexes_fp(" ^
                           (tmp_gen "cur_ch") ^
                           ", " ^ (List.nth_exn args 2) ^
                           "), " ^ (tmp_gen "vk1") ^ ", " ^
                           (tmp_gen "vk2") ^ "); @*/");
                        (fun {tmp_gen;_} ->
                           "/*@ coherent_same_cap(" ^
                           (tmp_gen "cur_map") ^ ", " ^ (tmp_gen "cur_ch") ^ ");@*/\n");
                        (fun {args;tmp_gen;_} ->
                           "//@ expire_olds_keeps_high_bounded(" ^
                           (tmp_gen "cur_ch") ^
                           ", " ^ (List.nth_exn args 2) ^
                           ");\n");
                        ];
                      lemmas_after = [
                        capture_chain_after "ch_after_exp" 0;
                        capture_map_after "map_after_exp" 1;
                        (fun params ->
                           "//@out_of_space_abstract(" ^
                           (params.tmp_gen "map_after_exp") ^
                           ", " ^ (params.tmp_gen "ch_after_exp") ^ ");");
                        (fun params ->
                           "//@ dmap<flow_id,flow_id,flow> map_after_expiration = " ^
                           (params.tmp_gen "map_after_exp") ^";\n" ^
                           "dchain chain_after_expiration = " ^
                           (params.tmp_gen "ch_after_exp") ^ ";";);
                      ];};
     "dchain_allocate_new_index", {ret_type = Static Sint32;
                                   arg_types = stt [Ptr dchain_struct; Ptr Sint32; time_t;];
                                   extra_ptr_types = [];
                                   lemmas_before = [
                                     capture_chain "cur_ch" 0;
                                   ];
                                   lemmas_after = [
                                     (fun {args;_} ->
                                        "time_for_allocated_index = " ^ (List.nth_exn args 2) ^
                                        ";\n");
                                     on_rez_nz
                                       (fun params ->
                                          "{\n allocate_preserves_index_range(" ^
                                          (params.tmp_gen "cur_ch") ^
                                          ", *" ^
                                          (List.nth_exn params.args 1) ^ ", " ^
                                          (List.nth_exn params.args 2) ^ ");\n}");
                                     (fun params ->
                                        "//@ allocate_keeps_high_bounded(" ^
                                        (params.tmp_gen "cur_ch") ^
                                        ", *" ^ (List.nth_exn params.args 1) ^
                                        ", " ^ (List.nth_exn params.args 2) ^
                                        ");\n");
                                     (fun params ->
                                        last_time_for_index_alloc :=
                                          (List.nth_exn params.args 2);
                                        "");
                                     (fun params ->
                                        "the_index_allocated = *" ^
                                        (List.nth_exn params.args 1) ^ ";\n");
                                   ];};
     "dchain_rejuvenate_index", {ret_type = Static Sint32;
                                 arg_types = stt [Ptr dchain_struct; Sint32; time_t;];
                                 extra_ptr_types = [];
                                 lemmas_before = [
                                   capture_chain "cur_ch" 0;
                                   (fun {args;tmp_gen;_} ->
                                      "/*@ {\n\
                                        assert map_vec_chain_coherent<\
                                       flow_id>(?" ^
                                      (tmp_gen "cur_map") ^ ", ?" ^
                                      (tmp_gen "cur_vec") ^ ", " ^
                                      (tmp_gen "cur_ch") ^
                                      ");\n\
                                       mvc_coherent_same_len(" ^
                                      (tmp_gen "cur_map") ^ ", " ^
                                      (tmp_gen "cur_vec") ^ ", " ^
                                      (tmp_gen "cur_ch") ^ ");\n} @*/");
                                   (fun {args;tmp_gen;_} ->
                                      "//@ rejuvenate_keeps_high_bounded(" ^
                                      (tmp_gen "cur_ch") ^
                                      ", " ^ (List.nth_exn args 1) ^
                                      ", " ^ (List.nth_exn args 2) ^
                                      ");\n");];
                                 lemmas_after = [
                                   (fun params ->
                                      "/*@ if (" ^ params.ret_name ^
                                      " != 0) { \n" ^
                                       "assert map_vec_chain_coherent<flow_id>\
                                       (?cur_map,?cur_vec,?cur_ch);\n" ^
                                      "mvc_rejuvenate_preserves_coherent(cur_map,\
                                       cur_vec, cur_ch, " ^
                                      (List.nth_exn params.args 1) ^ ", "
                                      ^ (List.nth_exn params.args 2) ^ ");\n\
                                       rejuvenate_preserves_index_range(cur_ch," ^
                                      (List.nth_exn params.args 1) ^ ", " ^
                                      (List.nth_exn params.args 2) ^ ");\n }@*/");
                                   (fun params ->
                                      "the_index_rejuvenated = " ^
                                      (List.nth_exn params.args 1) ^ ";\n");
                                 ];};
     "dchain_is_index_allocated", {ret_type = Static Sint32;
                                   arg_types = stt [Ptr dchain_struct;
                                                    Sint32];
                                   extra_ptr_types = [];
                                   lemmas_before = [];
                                   lemmas_after = [];};
     "stub_core_trace_rx", {
                 ret_type = Static Void;
                 arg_types = stt [Ptr (Ptr rte_mbuf_struct);];
                 extra_ptr_types = estt ["incoming_package",
                                         Ptr rte_mbuf_struct;
                                         "user_buf_addr",
                                         Ptr stub_mbuf_content_struct];
                 lemmas_before = [];
                 lemmas_after = [(fun params -> let arg0 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn params.args 0) in
                                       "a_packet_received = true;\n" ^
                                       simplify_c_string (
                                         "received_on_port = " ^
                                         "(*" ^ arg0 ^ ")->port;\n" ^
                                         "received_packet_type = " ^
                                         "(*" ^ arg0 ^ ")->packet_type;\n") ^
                                         (copy_stub_mbuf_content "the_received_packet"
                                          ("*" ^ arg0)));
                                 ];};
     "stub_core_trace_tx", {
                 ret_type = Static Uint8;
                 arg_types = stt [Ptr rte_mbuf_struct; Uint16];
                 extra_ptr_types = estt ["user_buf_addr",
                                         Ptr stub_mbuf_content_struct];
                 lemmas_before = [
                     (fun params ->
                          let sent_pkt =
                            Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn params.args 0)
                          in
                            (copy_stub_mbuf_content "sent_packet"
                             (sent_pkt)) ^ "\n" ^
                            simplify_c_string (
                              "sent_on_port = " ^ (List.nth_exn params.args 1) ^ ";\n" ^
                              "sent_packet_type = (" ^
                              sent_pkt ^ ")->packet_type;"));];
                 lemmas_after = [(fun _ -> "a_packet_sent = true;\n");];
                 };
     "stub_core_trace_free", {
                   ret_type = Static Void;
                   arg_types = stt [Ptr rte_mbuf_struct;];
                   extra_ptr_types = estt ["user_buf_addr",
                                           Ptr stub_mbuf_content_struct];
                   lemmas_before = [];
                   lemmas_after = [];}
    ]

(* TODO: make external_ip symbolic *)
module Iface : Fspec_api.Spec =
struct
  let preamble = "\
#include \"lib/expirator.h\"\n\
#include \"lib/stubs/time_stub_control.h\"\n\
#include \"lib/containers/double-map.h\"\n\
#include \"lib/containers/double-chain.h\"\n\
#include \"lib/stubs/containers/double-map-stub-control.h\"\n\
#include \"vignat/nat_loop.h\"\n\
//@ #include \"vignat/nat_abstract.h\"\n" ^
                  (In_channel.read_all "preamble.tmpl") ^
                  (In_channel.read_all "preamble_hide.tmpl") ^
                 "void to_verify()\n\
                  /*@ requires true; @*/ \n\
                  /*@ ensures true; @*/\n{\n\
                  int start_port;\n\
                  uint32_t external_ip = 0;\n\
                  uint16_t received_on_port;\n\
                  uint32_t received_packet_type;\n\
                  int the_index_allocated = -1;\n\
                  int the_index_rejuvenated = -1;\n\
                  int64_t time_for_allocated_index = 0;\n\
                  struct stub_mbuf_content the_received_packet;\n\
                  bool a_packet_received = false;\n\
                  struct stub_mbuf_content sent_packet;\n\
                  uint16_t sent_on_port;\n\
                  uint32_t sent_packet_type;\n\
                  bool a_packet_sent = false;\n\
                  bool keys_v_allocated = false;\n\
                  bool keys_v_borrowed = false;\n\
                  bool values_v_borrowed = false;\n\
                 "
  let fun_types = fun_types
  let boundary_fun = "loop_invariant_produce"
  let finishing_fun = "loop_invariant_consume"
  let eventproc_iteration_begin = "loop_invariant_produce"
  let eventproc_iteration_end = "loop_invariant_consume"
  let user_check_for_complete_iteration =
    ""(*TODO: (In_channel.read_all "forwarding_property.tmpl") *)
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

