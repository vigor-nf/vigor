open Core
open Str
open Fspec_api
open Ir

type map_key = Int | Ext

let last_index_gotten = ref ""
let last_index_key = ref Int
let last_indexing_succ_ret_var = ref ""
let last_time_for_index_alloc = ref ""


let capture_a_map t name {tmp_gen;_} =
  "//@ assert mapp<" ^ t ^ ">(_, _, _, _, mapc(_,?" ^ (tmp_gen name) ^ ", _));\n"

let capture_chain_after ch_name ptr_num (params:lemma_params) =
  "//@ assert double_chainp(?" ^ (params.tmp_gen ch_name) ^ ", " ^
  (List.nth_exn params.args ptr_num) ^ ");\n"

let capture_chain ch_name ptr_num {args;tmp_gen;_} =
  "//@ assert double_chainp(?" ^ (tmp_gen ch_name) ^ ", " ^
  (List.nth_exn args ptr_num) ^ ");\n"

let packet_struct = Ir.Str ("Packet", [])
let map_struct = Ir.Str ("Map", [])
let vector_struct = Ir.Str ( "Vector", [] )
let dchain_struct = Ir.Str ( "DoubleChain", [] )
let flow_id_struct = Ir.Str ( "FlowId", ["src_port", Uint16;
                                         "dst_port", Uint16;
                                         "src_ip", Uint32;
                                         "dst_ip", Uint32;
                                         "internal_device", Uint16;
                                         "protocol", Uint8;] )

let ether_addr_struct = Ir.Str ( "ether_addr", ["addr_bytes", Array Uint8;])
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
let tcpudp_hdr_struct = Ir.Str ("tcpudp_hdr", ["src_port", Uint16;
                                               "dst_port", Uint16])
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
                           tx_bl
                              "{\n\
                                produce_function_pointer_chunk vector_init_elem<flow_id>(flow_id_allocate)\
                                (flow_idp, sizeof(struct FlowId))(a) \
                                {\
                                call();\
                                }\n\
                               }\n";
                           (fun {args;_} ->
                              "/*@ { \n\
                               assume(sizeof(struct FlowId) == " ^
                              (List.nth_exn args 0) ^
                              ");\n } @*/ ");
                         ];
                         lemmas_after = [
                           (fun {tmp_gen;ret_name;_} ->
                              "/*@ if (" ^ ret_name ^
                              ") {\n\
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
                               }@*/");
                           ];};
     "vector_borrow",      {ret_type = Static Void;
                            arg_types = stt [Ptr vector_struct;
                                             Sint32;
                                             Ptr (Ptr flow_id_struct);];
                            extra_ptr_types = estt ["borrowed_cell", Ptr flow_id_struct;];
                            lemmas_before = [
                              (fun params ->
                                   "//@ assert vectorp<flow_id>(" ^ (List.nth_exn params.args 0) ^
                                   ", flow_idp, ?" ^ (params.tmp_gen "vec") ^ ", ?" ^ (params.tmp_gen "veca") ^
                                   ");\n//@ vector_addrs_same_len_nodups(" ^ (List.nth_exn params.args 0) ^ ");\n")
                            ];
                            lemmas_after = [
                              (fun params ->
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
                                   ");\n} @*/ ")
                            ];};
     "vector_return",      {ret_type = Static Void;
                            arg_types = stt [Ptr vector_struct;
                                             Sint32;
                                             Ptr flow_id_struct;];
                            extra_ptr_types = [];
                            lemmas_before = [
                              (fun params ->
                                 "/*@ { assert vector_accp<flow_id>(_, _, ?" ^ (params.tmp_gen "vec") ^
                                 ", _, _, _); \n update_id(" ^
                                 (List.nth_exn params.args 1) ^ ", " ^
                                 (params.tmp_gen "vec") ^ "); } @*/");
                            ];
                            lemmas_after = [];};
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
                                                 Uint32;
                                                 Sint64;
                                                 Sint32;
                                                 Sint32;
                                                 Uint32];
                                extra_ptr_types = [];
                                lemmas_before = [
                                  (fun {args;_} ->
                                     "start_port = " ^ List.nth_exn args 6 ^ ";");
                                  (fun {args;_} ->
                                     "external_addr = " ^ List.nth_exn args 7 ^ ";");
                                  (fun {args;_} ->
                                     "/*@ close evproc_loop_invariant(*" ^
                                     List.nth_exn args 0 ^ ", *" ^
                                     List.nth_exn args 1 ^ ", *" ^
                                     List.nth_exn args 2 ^ ", " ^
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
                                                 Ptr Uint32;
                                                 Ptr Sint64;
                                                 Sint32;
                                                 Sint32;
                                                 Uint32];
                                extra_ptr_types = [];
                                lemmas_before = [];
                                lemmas_after = [
                                  (fun {args;_} ->
                                     "/*@ open evproc_loop_invariant (*" ^
                                     (List.nth_exn args 0) ^ ", *" ^
                                     (List.nth_exn args 1) ^ ", *" ^
                                     (List.nth_exn args 2) ^ ", *" ^
                                     (List.nth_exn args 3) ^ ", *" ^
                                     (List.nth_exn args 4) ^ ", " ^
                                     (List.nth_exn args 5) ^ ", " ^
                                     (List.nth_exn args 6) ^ ", " ^
                                     (List.nth_exn args 7) ^ "); @*/");
                                  (fun params ->
                                     "start_port = " ^ List.nth_exn params.args 6 ^ ";");
                                  (fun {args;_} ->
                                     "external_addr = " ^ List.nth_exn args 7 ^ ";");
                                  (fun {tmp_gen;args;_} ->
                                     "\n/*@ {\n\
                                      assert mapp<flow_id>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "fm") ^
                                     ", _));\n\
                                      assert vectorp<flow_id>(_, _, ?" ^ (tmp_gen "fvk") ^
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
                                     ");\n" ^
                                     "assert mapp<flow_id>(_ "^
                                     ", _, _, _, mapc(_, ?" ^ (tmp_gen "initial_flow_map") ^
                                     ", _));\n" ^
                                     "assert vectorp<flow_id>(_" ^
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
                        "->internal_device, " ^ arg1 ^
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
                         flow_id " ^ (tmp_gen "ea") ^ " = flid(" ^ arg1 ^
                        "->src_port, " ^ arg1 ^
                        "->dst_port, " ^ arg1 ^
                        "->src_ip, " ^ arg1 ^
                        "->dst_ip, " ^ arg1 ^
                        "->internal_device, " ^ arg1 ^
                        "->protocol);\n\
                         mvc_coherent_put<flow_id>(" ^ (tmp_gen "dm") ^
                        ", " ^ (tmp_gen "dv") ^
                        ", " ^ (tmp_gen "dh") ^
                        ", " ^ (List.nth_exn args 2) ^
                        ", time_for_allocated_index, " ^ (tmp_gen "ea") ^
                        ");\n\
                         } @*/\n"
                      );];};
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
                                     on_rez_nz
                                       (fun {args;tmp_gen;_} ->
                                          "{\n\
                                           assert map_vec_chain_coherent<\
                                           flow_id>(?" ^
                                          (tmp_gen "cur_map") ^ ", ?" ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^
                                          ");\n\
                                           mvc_coherent_alloc_is_halfowned<flow_id>(" ^
                                          (tmp_gen "cur_map") ^ ", " ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^ ", *" ^
                                          (List.nth_exn args 1) ^ ");\n}");
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
     "packet_receive", {ret_type = Static Boolean;
                        arg_types = stt [Uint16; Ptr (Ptr packet_struct);];
                        extra_ptr_types = [];
                        lemmas_before = [];
                        lemmas_after = [
                          (fun {args;ret_name;_} ->
                             "a_packet_received = " ^ ret_name ^ " ;\n" ^
                             "received_on_port = " ^ (List.nth_exn args 0) ^ ";\n"
                          )
                        ];};
     "packet_send", {ret_type = Static Void;
                     arg_types = stt [Ptr packet_struct; Uint16];
                     extra_ptr_types = [];
                     lemmas_before = [];
                     lemmas_after = [(fun {args;_} ->
                         "a_packet_sent = true;\n" ^
                         "sent_on_port = " ^ (List.nth_exn args 1) ^ ";\n" 
                       )];};
     "packet_get_port", {ret_type = Static Uint16;
                         arg_types = stt [Ptr packet_struct];
                         extra_ptr_types = [];
                         lemmas_before = [];
                         lemmas_after = [];};
     "packet_is_ipv4", {ret_type = Static Uint32;
                        arg_types = stt [Ptr packet_struct];
                        extra_ptr_types = [];
                        lemmas_before = [];
                        lemmas_after = [(fun {ret_name;_} ->
                            "is_ipv4 = " ^ ret_name ^ " != 0;\n"
                          )];};
     "packet_borrow_next_chunk", {ret_type = Static Void;
                                  arg_types = [Static (Ptr packet_struct);
                                               Static Uint32;
                                               Dynamic ["ether_hdr",
                                                        Ptr (Ptr ether_hdr_struct);
                                                        "ipv4_hdr",
                                                        Ptr (Ptr ipv4_hdr_struct);
                                                        "tcpudp_hdr",
                                                        Ptr (Ptr tcpudp_hdr_struct);
                                                        "ipv4_options",
                                                        Ptr (Ptr Sint8)
                                                       ]];
                                  extra_ptr_types =
                                    ["the_chunk",
                                     Dynamic ["ether_hdr",
                                              Ptr ether_hdr_struct;
                                              "ipv4_hdr",
                                              Ptr ipv4_hdr_struct;
                                              "tcpudp_hdr",
                                              Ptr tcpudp_hdr_struct;
                                              "ipv4_options",
                                              Ptr Sint8
                                             ]];
                                  lemmas_before = [];
                                  lemmas_after = [
                                    (fun {args;arg_types;_} ->
                                       match (List.nth_exn arg_types 2) with
                                       | Ptr (Ptr (Str (_,_))) ->
                                         "//@ close_struct(*" ^ (List.nth_exn args 2) ^ ");\n"
                                       | _ -> ""
                                    );
                                    (fun {args;arg_types;_} ->
                                       match List.nth_exn arg_types 2 with
                                       | Ptr (Ptr (Str ("ether_hdr", _))) ->
                                         "//@ recv_headers = add_ether_header(recv_headers, *" ^ (List.nth_exn args 2) ^ ");\n" ^
                                         "//@ open ether_hdrp(*" ^ (List.nth_exn args 2) ^
                                         ", _);\n\
                                          //@ open ether_addrp((" ^ (List.nth_exn args 2) ^
                                         "->s_addr), _);\n\
                                          //@ open ether_addrp((" ^ (List.nth_exn args 2) ^
                                         "->d_addr), _);\n"
                                       | Ptr (Ptr (Str ("ipv4_hdr", _))) ->
                                         "//@ recv_headers = add_ipv4_header(recv_headers, *" ^ (List.nth_exn args 2) ^ ");\n"
                                       | Ptr (Ptr (Str ("tcpudp_hdr", _))) ->
                                         "//@ recv_headers = add_tcpudp_header(recv_headers, *" ^ (List.nth_exn args 2) ^ ");\n"
                                       | Ptr (Ptr Sint8) ->
                                         ""
                                       | _ -> failwith "unsupported chunk type in packet_borrow_next_chunk"
                                      )];};
     "packet_return_chunk", {ret_type = Static Void;
                             arg_types = [Static (Ptr packet_struct);
                                          Dynamic ["ether_hdr",
                                                   Ptr ether_hdr_struct;
                                                   "ipv4_hdr",
                                                   Ptr ipv4_hdr_struct;
                                                   "tcpudp_hdr",
                                                   Ptr tcpudp_hdr_struct;
                                                   "ipv4_options",
                                                   Ptr Sint8
                                                  ]];
                             extra_ptr_types = [];
                             lemmas_before = [
                               (fun {arg_exps;arg_types;_} ->
                                  match List.nth_exn arg_types 1 with
                                  | Ptr (Str ("ether_hdr", _)) ->
                                    "//@ sent_headers = add_ether_header(sent_headers, " ^
                                    (render_tterm (List.nth_exn arg_exps 1)) ^
                                    ");\n\
                                     //@ open ether_hdrp(" ^
                                    (render_tterm (List.nth_exn arg_exps 1)) ^
                                    ", _);\n\
                                     //@ open ether_addrp(&(" ^
                                    (render_tterm (List.nth_exn arg_exps 1)) ^
                                    "->s_addr), _);\n
                                     //@ open ether_addrp(&(" ^
                                    (render_tterm (List.nth_exn arg_exps 1)) ^
                                    "->d_addr), _);\n"
                                  | Ptr (Str ("ipv4_hdr", _)) ->
                                    "//@ sent_headers = add_ipv4_header(sent_headers, " ^
                                    (render_tterm (List.nth_exn arg_exps 1)) ^
                                    ");\n"
                                  | Ptr (Str ("tcpudp_hdr", _)) ->
                                    "//@ sent_headers = add_tcpudp_header(sent_headers, " ^
                                    (render_tterm (List.nth_exn arg_exps 1)) ^
                                    ");\n"
                                  | Ptr Sint8 ->
                                    ""
                                  | _ -> failwith "unsupported chunk type in packet_return_chunk"
                               );
                                (fun {arg_exps;arg_types;_} ->
                                  match (List.nth_exn arg_types 1) with
                                  | Ptr (Str (_, _)) ->
                                    "//@ open_struct(" ^
                                    (render_tterm (List.nth_exn arg_exps 1))
                                    ^ ");\n"
                                  | _ -> ""
                                    )];
                             lemmas_after = [];};
     "packet_get_unread_length", {ret_type = Static Uint32;
                                  arg_types = stt [Ptr packet_struct];
                                  extra_ptr_types = [];
                                  lemmas_before = [];
                                  lemmas_after = [];};
     "packet_free", {
                   ret_type = Static Void;
                   arg_types = stt [Ptr packet_struct;];
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
#include \"vignat/nat_loop.h\"\n" ^
                  (In_channel.read_all "preamble.tmpl") ^
                 "void to_verify()\n\
                  /*@ requires true; @*/ \n\
                  /*@ ensures true; @*/\n{\n\
                  int start_port;\n\
                  int external_addr;\n\
                  uint32_t external_ip = 0;\n\
                  uint16_t received_on_port;\n\
                  int the_index_allocated = -1;\n\
                  int the_index_rejuvenated = -1;\n\
                  int64_t time_for_allocated_index = 0;\n\
                  bool a_packet_received = false;\n\
                  bool is_ipv4 = false;\n\
                  uint16_t sent_on_port;\n\
                  bool a_packet_sent = false;\n\
                  //@ dchain flow_chain;\n\
                  //@ list<pair<flow_id, int> > flow_map;\n\
                  //@ list<pair<flow_id, real> > flow_vec;\n\
                  //@ list<phdr> recv_headers = nil; \n\
                  //@ list<phdr> sent_headers = nil; \n\
                  //@ assume(sizeof(struct ether_hdr) == 14);
                  //@ assume(sizeof(struct tcpudp_hdr) == 4);
                  //@ assume(sizeof(struct ipv4_hdr) == 20);//TODO: handle all this sizeof's explicitly
                 "
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

