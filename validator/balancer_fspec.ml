open Str
open Core
open Fspec_api
open Ir

type map_key = Int | Ext

let capture_chain ch_name ptr_num {args;tmp_gen;_} =
  "//@ assert double_chainp(?" ^ (tmp_gen ch_name) ^ ", " ^
  (List.nth_exn args ptr_num) ^ ");\n"

let capture_a_chain name {tmp_gen;_} =
  "//@ assert double_chainp(?" ^ (tmp_gen name) ^", _);\n"

let capture_a_map t name {tmp_gen;_} =
  "//@ assert mapp<" ^ t ^ ">(_, _, _, _, mapc(_,?" ^ (tmp_gen name) ^ ", _));\n"

let capture_a_vector t name {tmp_gen;_} =
  "//@ assert vectorp<" ^ t ^ ">(_, _, ?" ^ (tmp_gen name) ^ ", _);\n"

let map_struct = Ir.Str ("Map", [])
let vector_struct = Ir.Str ( "Vector", [] )
let dchain_struct = Ir.Str ( "DoubleChain", [] )

let ether_addr_struct = Ir.Str ( "ether_addr", ["addr_bytes", Array (Uint8, 6);])
let lb_flow_struct = Ir.Str ( "LoadBalancedFlow", ["src_ip", Uint32;
                                                   "dst_ip", Uint32;
                                                   "src_port", Uint16;
                                                   "dst_port", Uint16;
                                                   "protocol", Uint8;])
let lb_backend_struct = Ir.Str ( "LoadBalancedBackend", ["nic", Uint16;
                                                         "mac", ether_addr_struct;
                                                         "ip", Uint32])

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
(* FIXME: for lb only ether_hdr is needed, the other two are here,
   just because rte_stubs.c dumps them for the other NF (NAT), and validator
   ensures we read everything dumped.*)
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

let copy_stub_mbuf_content var_name ptr =
  ("struct stub_mbuf_content* tmp_ub_ptr" ^ var_name ^
   " = (" ^ ptr ^ ")->buf_addr;\n") ^
  deep_copy
    {Ir.name=var_name;
     Ir.value={v=Deref {v=Ir.Id ("tmp_ub_ptr" ^ var_name);
                        t=Ptr stub_mbuf_content_struct};
               t=stub_mbuf_content_struct}}

(* VeriFast's C parser is quite limited, so simplify stuff... this is very brittle since it does no lookbehind to avoid accidents *)
let rec simplify_c_string str =
  let str0 = Str.global_replace (Str.regexp "\\*&") "" str in (* *&a  ==>  a *)
  let str0 = Str.global_replace (Str.regexp "\\*(&\\([^)]+\\))") "\\1" str0 in (* * (&a)  ==>  a *)
  let str0 = Str.global_replace (Str.regexp "&(\\([^)]+\\))->\\([^)]+\\)") "\\1.\\2" str0 in (* &a->b  ==>  a.b *)
  let str0 = Str.global_replace (Str.regexp "(&(\\([^)]+\\)))->\\([^)]+\\)") "\\1.\\2" str0 in (* (&a)->b  ==>  a.b *)
  let str0 = Str.global_replace (Str.regexp "(\\*\\([^)]+\\).\\([^)]+\\)") "\\1->\\2" str0 in (* ( *a ).b  ==>  a->b *)
  if str = str0 then str else simplify_c_string str0 (* find a fixpoint *)

let fun_types =
  String.Map.of_alist_exn
    ["current_time", {ret_type = Static Sint64;
                      arg_types = [];
                      extra_ptr_types = [];
                      lemmas_before = [];
                      lemmas_after = [
                        (fun params ->
                           "int64_t now = " ^ (params.ret_name) ^ ";\n")];};
     "lb_flow_hash", {ret_type = Static Uint32;
                      arg_types = stt [Ptr lb_flow_struct];
                      extra_ptr_types = [];
                      lemmas_before = [];
                      lemmas_after = [];};
     "lb_loop_invariant_consume", {ret_type = Static Void;
                                   arg_types = stt
                                           [Ptr (Ptr map_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr dchain_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr map_struct);
                                            Ptr (Ptr dchain_struct);
                                            Ptr (Ptr vector_struct);
                                            Sint64;
                                            Uint32;
                                            Uint32];
                                       extra_ptr_types = [];
                                       lemmas_before = [
                                         (fun {args;_} ->
                                            "/*@ close lb_loop_invariant(*" ^
                                            (List.nth_exn args 0) ^ ", *" ^
                                            (List.nth_exn args 1) ^ ", *" ^
                                            (List.nth_exn args 2) ^ ", *" ^
                                            (List.nth_exn args 3) ^ ", *" ^
                                            (List.nth_exn args 4) ^ ", *" ^
                                            (List.nth_exn args 5) ^ ", *" ^
                                            (List.nth_exn args 6) ^ ", *" ^
                                            (List.nth_exn args 7) ^ ", *" ^
                                            (List.nth_exn args 8) ^ ", " ^
                                            (List.nth_exn args 9) ^ ", " ^
                                            (List.nth_exn args 10) ^ ", " ^
                                            (List.nth_exn args 11) ^ "); @*/");];
                                       lemmas_after = [];};
     "lb_loop_invariant_produce", {ret_type = Static Void;
                                       arg_types = stt
                                           [Ptr (Ptr map_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr dchain_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr map_struct);
                                            Ptr (Ptr dchain_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr Sint64;
                                            Uint32;
                                            Uint32];
                                       extra_ptr_types = [];
                                       lemmas_before = [];
                                       lemmas_after = [
                                         (fun {args;_} ->
                                            "/*@ open lb_loop_invariant (*" ^
                                            (List.nth_exn args 0) ^ ", *" ^
                                            (List.nth_exn args 1) ^ ", *" ^
                                            (List.nth_exn args 2) ^ ", *" ^
                                            (List.nth_exn args 3) ^ ", *" ^
                                            (List.nth_exn args 4) ^ ", *" ^
                                            (List.nth_exn args 5) ^ ", *" ^
                                            (List.nth_exn args 6) ^ ", *" ^
                                            (List.nth_exn args 7) ^ ", *" ^
                                            (List.nth_exn args 8) ^ ", *" ^
                                            (List.nth_exn args 9) ^ ", " ^
                                            (List.nth_exn args 10) ^ ", " ^
                                            (List.nth_exn args 11) ^ "); @*/");
                                         (fun {tmp_gen;_} ->
                                            "\n/*@ {\n\
                                             assert mapp<lb_flowi>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "fi") ^ ", _));\n\
                                             assert vectorp<lb_flowi>(_, _, ?" ^ (tmp_gen "fh") ^ ", _);\n\
                                             assert vectorp<lb_backendi>(_, _, ?" ^ (tmp_gen "fb") ^ ", _);\n\
                                             assert map_vec_chain_coherent<lb_flowi>(" ^
                                            (tmp_gen "fi") ^ ", " ^
                                            (tmp_gen "fh") ^ ", ?" ^
                                            (tmp_gen "ch") ^
                                            ");\n\
                                             mvc_coherent_same_len<lb_flowi>(" ^ 
                                                   (tmp_gen "fi") ^
                                            ", " ^ (tmp_gen "fh") ^
                                            ", " ^ (tmp_gen "ch") ^
                                            ");\n\
                                             assert mapp<lb_flowi>(_, _, _, _, ?" ^ (tmp_gen "fi_full") ^ ");\n" ^ 
                                            "initial_indices = " ^ (tmp_gen "fi_full") ^
                                            ";\ninitial_heap = " ^ (tmp_gen "fh") ^
                                            ";\ninitial_backends = " ^ (tmp_gen "fb") ^
                                            ";\ninitial_chain = " ^ (tmp_gen "ch") ^
                                            ";\n} @*/");
                                       ];};
     "dchain_allocate", {ret_type = Static Sint32;
                         arg_types = stt [Sint32; Ptr (Ptr dchain_struct)];
                         extra_ptr_types = [];
                         lemmas_before = [];
                         lemmas_after = [
                           on_rez_nonzero
                             "if (!dchain_flow_allocated) {\n\
                              assert vectorp<lb_flowi>(_, _, ?allocated_vector, _);\n\
                              empty_map_vec_dchain_coherent\
                              <lb_flowi>(allocated_vector);\n\
                              } else {\n\
                              assert vectorp<uint32_t>(the_ip_vector, u_integer, ?allocated_ip_vector, _);\n\
                              empty_map_vec_dchain_coherent\
                              <uint32_t>(allocated_ip_vector);\n\
                              }";
                           (fun _ -> "dchain_flow_allocated = true;");
                           tx_l "index_range_of_empty(65536, 0);";];};
     "dchain_allocate_new_index", {ret_type = Static Sint32;
                                   arg_types = stt [Ptr dchain_struct; Ptr Sint32; Uint32;];
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
                                        "the_index_allocated = *" ^
                                        (List.nth_exn params.args 1) ^ ";\n");
                                     on_rez_nz
                                       (fun {args;tmp_gen;_} ->
                                          "if (last_map_accessed_lb_flowi) {\n\
                                           assert map_vec_chain_coherent<\
                                           lb_flowi>(?" ^
                                          (tmp_gen "cur_map") ^ ", ?" ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^
                                          ");\n\
                                           mvc_coherent_alloc_is_halfowned<lb_flowi>(" ^
                                          (tmp_gen "cur_map") ^ ", " ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^ ", *" ^
                                          (List.nth_exn args 1) ^ ");\n} else " ^
                                          "{\n\
                                           assert map_vec_chain_coherent<\
                                           uint32_t>(?" ^
                                          (tmp_gen "cur_map") ^ ", ?" ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^
                                          ");\n\
                                           mvc_coherent_alloc_is_halfowned<uint32_t>(" ^
                                          (tmp_gen "cur_map") ^ ", " ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^ ", *" ^
                                          (List.nth_exn args 1) ^ ");\n}");
                                   ];};
     "dchain_rejuvenate_index", {ret_type = Static Sint32;
                                 arg_types = stt [Ptr dchain_struct;
                                                  Sint32; Uint32;];
                                 extra_ptr_types = [];
                                 lemmas_before = [
                                   capture_chain "cur_ch" 0;
                                   (fun {tmp_gen;_} ->
                                      "/*@ if (last_map_accessed_lb_flowi) {\n\
                                        assert map_vec_chain_coherent<\
                                       lb_flowi>(?" ^
                                      (tmp_gen "cur_map") ^ ", ?" ^
                                      (tmp_gen "cur_vec") ^ ", " ^
                                      (tmp_gen "cur_ch") ^
                                      ");\n\
                                       mvc_coherent_same_len(" ^
                                      (tmp_gen "cur_map") ^ ", " ^
                                      (tmp_gen "cur_vec") ^ ", " ^
                                      (tmp_gen "cur_ch") ^ ");\n} else {" ^
                                        "assert map_vec_chain_coherent<\
                                       uint32_t>(?" ^
                                      (tmp_gen "cur_map") ^ ", ?" ^
                                      (tmp_gen "cur_vec") ^ ", " ^
                                      (tmp_gen "cur_ch") ^
                                      ");\n\
                                       mvc_coherent_same_len(" ^
                                      (tmp_gen "cur_map") ^ ", " ^
                                      (tmp_gen "cur_vec") ^ ", " ^
                                      (tmp_gen "cur_ch") ^ ");\n} @*/";);
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
                                      "if (last_map_accessed_lb_flowi) {\n\
                                       assert map_vec_chain_coherent<lb_flowi>\
                                       (?cur_map,?cur_vec,?cur_ch);\n" ^
                                      "mvc_rejuvenate_preserves_coherent(cur_map,\
                                       cur_vec, cur_ch, " ^
                                      (List.nth_exn params.args 1) ^ ", "
                                      ^ (List.nth_exn params.args 2) ^ ");\n\
                                       rejuvenate_preserves_index_range(cur_ch," ^
                                      (List.nth_exn params.args 1) ^ ", " ^
                                      (List.nth_exn params.args 2) ^ ");\n } else {\n" ^
                                       "assert map_vec_chain_coherent<uint32_t>\
                                       (?cur_map,?cur_vec,?cur_ch);\n" ^
                                      "mvc_rejuvenate_preserves_coherent(cur_map,\
                                       cur_vec, cur_ch, " ^
                                      (List.nth_exn params.args 1) ^ ", "
                                      ^ (List.nth_exn params.args 2) ^ ");\n\
                                       rejuvenate_preserves_index_range(cur_ch," ^
                                      (List.nth_exn params.args 1) ^ ", " ^
                                      (List.nth_exn params.args 2) ^
                                      ");\n}\n}@*/");
                                   (fun params ->
                                      "int the_index_rejuvenated = " ^
                                      (List.nth_exn params.args 1) ^ ";\n");
                                 ];};

     "dchain_is_index_allocated", {ret_type = Static Sint32;
                                   arg_types = stt [Ptr dchain_struct;
                                                    Sint32];
                                   extra_ptr_types = [];
                                   lemmas_before = [];
                                   lemmas_after = [];};
     "expire_items_single_map", {ret_type = Static Sint32;
                                 arg_types = stt [Ptr dchain_struct;
                                                  Ptr vector_struct;
                                                  Ptr map_struct;
                                                  Uint32];
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
                                   tx_l
                                      "if (!map_flow_expired) {\n\
                                       } else {\n\
                                       close hide_mapp<lb_flowi>(_, _, _, _, _);\n\
                                       }";
                                 ];
                                 lemmas_after = [
                                   (fun _ -> "if (!map_flow_expired) {\n\
                                              map_flow_expired = true;\n\
                                              } else {\n\
                                              //@ open hide_mapp<lb_flowi>(_, _, _, _, _);\n\
                                              }");
                                   (fun {tmp_gen;_} ->
                                      "/*@ {\n\
                                       assert mapp<lb_flowi>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "fi") ^ ", _));\n\
                                       assert vectorp<lb_flowi>(_, _, ?" ^ (tmp_gen "fh") ^ ", _);\n\
                                       assert vectorp<lb_backendi>(_, _, ?" ^ (tmp_gen "fb") ^ ", _);\n\
                                       assert map_vec_chain_coherent<lb_flowi>(" ^
                                      (tmp_gen "fi") ^ ", " ^
                                      (tmp_gen "fh") ^ ", ?" ^
                                      (tmp_gen "ch") ^
                                      ");\n\
                                       assert mapp<lb_flowi>(_, _, _, _, ?" ^ (tmp_gen "fi_full") ^ ");\n\
                                      mvc_coherent_same_len<lb_flowi>(" ^
                                      (tmp_gen "fi") ^ ", " ^
                                      (tmp_gen "fh") ^ ", " ^
                                      (tmp_gen "ch") ^ ");\n\
                                      expired_indices = " ^ (tmp_gen "fi_full") ^ ";\n\
                                      expired_heap = " ^ (tmp_gen "fh") ^ ";\n\
                                      expired_backends = " ^ (tmp_gen "fb") ^ ";\n\
                                      expired_chain = " ^ (tmp_gen "ch") ^ ";\n} @*/"
                                         );
                                 ];};
     "map_allocate", {ret_type = Static Sint32;
                      arg_types = stt [Fptr "map_keys_equality";
                                       Fptr "map_key_hash";
                                       Uint32;
                                       Ptr (Ptr map_struct)];
                      extra_ptr_types = [];
                      lemmas_before = [
                        (fun _ -> (* VeriFast will syntax-error on produce_function_pointer_chunk if not within a block *)
                            "/*@ if (!map_flow_allocated) {\nproduce_function_pointer_chunk \
                            map_keys_equality<lb_flowi>(lb_flow_equality)\
                            (lb_flowp)(a, b) \
                            {\
                            call();\
                            }\n\
                            produce_function_pointer_chunk \
                            map_key_hash<lb_flowi>(lb_flow_hash)\
                            (lb_flowp, lb_flow_hash_2)(a) \
                            {\
                            call();\
                            }\n\
                             } else {\nproduce_function_pointer_chunk \
                            map_keys_equality<uint32_t>(lb_ip_equality)\
                            (u_integer)(a, b) \
                            {\
                            call();\
                            }\n\
                            produce_function_pointer_chunk \
                            map_key_hash<uint32_t>(lb_ip_hash)\
                            (u_integer, lb_ip_hash_fp)(a) \
                            {\
                            call();\
                            }\n\
                            } @*/ \n");];
                      lemmas_after = [
                        (fun {tmp_gen;ret_name;_} -> (* see remark above *)
                            "/*@ if (!map_flow_allocated) {\n assert [?" ^ (tmp_gen "imkedy") ^
                           "]is_map_keys_equality(lb_flow_equality,\
                            lb_flowp);\n\
                            close [" ^ (tmp_gen "imkedy") ^
                           "]hide_is_map_keys_equality(lb_flow_equality, \
                            lb_flowp);\n\
                            assert [?" ^ (tmp_gen "imkhdy") ^
                           "]is_map_key_hash(lb_flow_hash,\
                            lb_flowp, lb_flow_hash_2);\n\
                            close [" ^ (tmp_gen "imkhdy") ^
                           "]hide_is_map_key_hash(lb_flow_hash, \
                            lb_flowp, lb_flow_hash_2);\n\
                            } else {\n assert [?" ^ (tmp_gen "imkedy") ^
                           "]is_map_keys_equality(lb_ip_equality,\
                            u_integer);\n\
                            close [" ^ (tmp_gen "imkedy") ^
                           "]hide_is_map_keys_equality(lb_ip_equality, \
                            u_integer);\n\
                            assert [?" ^ (tmp_gen "imkhdy") ^
                           "]is_map_key_hash(lb_ip_hash,\
                            u_integer, lb_ip_hash_fp);\n\
                            close [" ^ (tmp_gen "imkhdy") ^
                           "]hide_is_map_key_hash(lb_ip_hash, \
                            u_integer, lb_ip_hash_fp);\n\
                            if (" ^ ret_name ^
                            " == 1) {\n\
                            assert mapp<uint32_t>(_, _, _, _, mapc(?" ^ (tmp_gen "cap") ^
                            ", ?" ^ (tmp_gen "map") ^
                            ", ?" ^ (tmp_gen "addr_map") ^
                            "));\n\
                             assert vectorp<uint32_t>(the_ip_vector, _, ?" ^
                            (tmp_gen "dks") ^
                            ", ?" ^ (tmp_gen "dkaddrs") ^
                            ");\n\
                             empty_kkeeper(" ^
                            (tmp_gen "dkaddrs") ^
                            ", " ^ (tmp_gen "dks") ^
                            ", " ^ (tmp_gen "addr_map") ^
                            ", " ^ (tmp_gen "cap") ^
                            ");\n\
                             }\n\
                            } @*/");
                        (fun _ -> "map_flow_allocated = true;")];};
     "map_get", {ret_type = Static Sint32;
                 arg_types = [Static (Ptr map_struct);
                              Dynamic ["LoadBalancedFlow", (Ptr lb_flow_struct);
                                       "uint32_t", Ptr Uint32];
                              Static (Ptr Sint32)];
                 extra_ptr_types = [];
                 lemmas_before = [
                   (fun ({arg_types;arg_exps;tmp_gen;_} as params) ->
                      match List.nth_exn arg_types 1 with
                      | Ptr (Str ("LoadBalancedFlow", _)) ->
                        "//@ assert lb_flowp(" ^ (render_tterm (List.nth_exn arg_exps 1)) ^
                        ", ?" ^ (tmp_gen "dk") ^ ");\n" ^
                        (capture_a_chain "dh" params ^
                         capture_a_map "lb_flowi" "dm" params ^
                         capture_a_vector "lb_flowi" "dv" params) ^
                        "/*@ { close hide_mapp<uint32_t>(_, u_integer, _, _, _); } @*/\n"
                      | Ptr Uint32 ->
                         capture_a_map "uint32_t" "dm" params ^
                         "//@ assert map_vec_chain_coherent<uint32_t>(" ^
                         (tmp_gen "dm") ^ ", ?" ^
                         (tmp_gen "dv") ^ ", ?" ^
                         (tmp_gen "dh") ^ ");\n" ^
                        "/*@ { close hide_mapp<lb_flowi>(_, lb_flowp, _, _, _); } @*/\n"
                      | _ -> failwith "unexpected key type for map_get.");];
                 lemmas_after = [
                   (fun {arg_types;ret_name;tmp_gen;args;_} ->
                      match List.nth_exn arg_types 1 with
                      | Ptr (Str ("LoadBalancedFlow", _)) ->
                        "/*@ if (" ^ ret_name ^
                        " != 0) {\n\
                         mvc_coherent_map_get_bounded(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ", " ^
                        (tmp_gen "dk") ^
                        ");\n\
                         mvc_coherent_map_get_vec_half(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ", " ^
                        (tmp_gen "dk") ^
                        ");\n\
                         } @*/\n\
                        last_map_accessed_lb_flowi = true;\n" ^
                        "/*@ { open hide_mapp<uint32_t>(_, u_integer, _, _, _); } @*/\n"
                      | Ptr Uint32 ->
                        "/*@ if (" ^ ret_name ^
                        " != 0) {\n\
                         mvc_coherent_map_get_bounded(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ", *" ^
                        (List.nth_exn args 1) ^
                        ");\n\
                         mvc_coherent_map_get_vec_half(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ", *" ^
                        (List.nth_exn args 1) ^
                        ");\n\
                         } @*/\n\
                        last_map_accessed_lb_flowi = false; \n" ^
                        "/*@ { open hide_mapp<lb_flowi>(_, lb_flowp, _, _, _); } @*/\n"
                      | _ -> failwith "unexpected key type for map_get.");
                   (fun params -> "if (" ^ params.ret_name ^ " != 0) { backend_known = true; backend_index = *" ^ (List.nth_exn params.args 2) ^ "; }\n" );];};
     "map_put", {ret_type = Static Void;
                 arg_types = [Static (Ptr map_struct);
                              Dynamic ["LoadBalancedFlow", (Ptr lb_flow_struct);
                                       "uint32_t", Ptr Uint32];
                              Static Sint32];
                 extra_ptr_types = [];
                 lemmas_before = [
                   (fun {args;tmp_gen;arg_types;_} ->
                      match List.nth_exn arg_types 1 with
                      | Ptr (Str ("LoadBalancedFlow", _)) ->
                        "\n//@ assert mapp<lb_flowi>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "dm") ^
                        ", _));\n" ^
                        "\n/*@ {\n\
                         assert map_vec_chain_coherent<lb_flowi>(" ^
                        (tmp_gen "dm") ^ ", ?" ^
                        (tmp_gen "dv") ^ ", ?" ^
                        (tmp_gen "dh") ^
                        ");\n\
                         mvc_coherent_dchain_non_out_of_space_map_nonfull<lb_flowi>(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ");\n} @*/\n" ^
                        let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
                        "/*@ { \n\
                         assert mapp<lb_flowi>(_, _, _, _, mapc(_, _, ?dm_addrs)); \n\
                         assert vector_accp<lb_flowi>(_, _, ?the_dv, ?dv_addrs, _, _); \n\
                         assert map_vec_chain_coherent<lb_flowi>(?the_dm, the_dv, ?the_dh);\n\
                         lb_flowi vvv = lb_flowc(" ^ arg1 ^
                        "->src_ip, " ^ arg1 ^
                        "->src_port, " ^ arg1 ^
                        "->dst_port, " ^ arg1 ^
                        "->protocol); \n\
                         mvc_coherent_key_abscent(the_dm, the_dv, the_dh, vvv);\n\
                         kkeeper_add_one(dv_addrs, the_dv, dm_addrs, vvv, " ^ (List.nth_exn args 2) ^
                        "); \n\
                         } @*/"
                      | Ptr Uint32 ->
                        "\n//@ assert mapp<uint32_t>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "dm") ^
                        ", _));\n" ^
                        "\n/*@ {\n\
                         assert map_vec_chain_coherent<uint32_t>(" ^
                        (tmp_gen "dm") ^ ", ?" ^
                        (tmp_gen "dv") ^ ", ?" ^
                        (tmp_gen "dh") ^
                        ");\n\
                         mvc_coherent_dchain_non_out_of_space_map_nonfull<uint32_t>(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ");\n} @*/\n" ^
                        let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
                        "/*@ { \n\
                         assert mapp<uint32_t>(_, _, _, _, mapc(_, _, ?dm_addrs)); \n\
                         assert vector_accp<uint32_t>(_, _, ?the_dv, ?dv_addrs, _, _); \n\
                         assert map_vec_chain_coherent<uint32_t>(?the_dm, the_dv, ?the_dh);\n\
                         uint32_t vvv = *" ^ arg1 ^
                        "; \n\
                         mvc_coherent_key_abscent(the_dm, the_dv, the_dh, vvv);\n\
                         kkeeper_add_one(dv_addrs, the_dv, dm_addrs, vvv, " ^ (List.nth_exn args 2) ^
                        "); \n\
                         } @*/\n" ^
                        "/*@ { close hide_mapp<lb_flowi>(_, lb_flowp, _, _, _); } @*/\n"
                      | _ -> failwith "unexpected key type for map_put.");];
                 lemmas_after = [
                   (fun {args;tmp_gen;arg_types;_} ->
                      match List.nth_exn arg_types 1 with
                      | Ptr (Str ("LoadBalancedFlow", _)) ->
                        let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
                        "\n/*@ {\n\
                         assert map_vec_chain_coherent<lb_flowi>(" ^ (tmp_gen "dm") ^
                        ", ?" ^ (tmp_gen "dv") ^
                        ", ?" ^ (tmp_gen "dh") ^
                        ");\n\
                         lb_flowi " ^ (tmp_gen "ea") ^ " = lb_flowc(" ^ arg1 ^
                        "->src_ip, " ^ arg1 ^
                        "->src_port, " ^ arg1 ^
                        "->dst_port, " ^ arg1 ^
                        "->protocol);\n\
                         mvc_coherent_put<lb_flowi>(" ^ (tmp_gen "dm") ^
                        ", " ^ (tmp_gen "dv") ^
                        ", " ^ (tmp_gen "dh") ^
                        ", " ^ (List.nth_exn args 2) ^
                        ", time_for_allocated_index, " ^ (tmp_gen "ea") ^
                        ");\n\
                         } @*/"
                      | Ptr Uint32 ->
                        let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
                        "\n/*@ {\n\
                         assert map_vec_chain_coherent<uint32_t>(" ^ (tmp_gen "dm") ^
                        ", ?" ^ (tmp_gen "dv") ^
                        ", ?" ^ (tmp_gen "dh") ^
                        ");\n\
                         uint32_t " ^ (tmp_gen "ea") ^ " = *" ^ arg1 ^
                        ";\n\
                         mvc_coherent_put<uint32_t>(" ^ (tmp_gen "dm") ^
                        ", " ^ (tmp_gen "dv") ^
                        ", " ^ (tmp_gen "dh") ^
                        ", " ^ (List.nth_exn args 2) ^
                        ", time_for_allocated_index, " ^ (tmp_gen "ea") ^
                        ");\n\
                         } @*/\n" ^
                        "/*@ { open hide_mapp<lb_flowi>(_, lb_flowp, _, _, _); } @*/\n"
                      | _ -> failwith "unexpected key type for map_put.");
                   (fun params -> "backend_known = true;\nbackend_index = " ^ (List.nth_exn params.args 2) ^ ";\n");];};
     "map_erase", {ret_type = Static Void;
                   arg_types = [Static (Ptr map_struct);
                                Dynamic ["LoadBalancedFlow", (Ptr lb_flow_struct);
                                         "uint32_t", Ptr Uint32];
                                Static (Ptr (Ptr Void));];
                  extra_ptr_types = [];
                  lemmas_before = [];
                  lemmas_after = [];};
     "map_size", {ret_type = Static Sint32;
                  arg_types = [Static (Ptr map_struct);];
                  extra_ptr_types = [];
                  lemmas_before = [];
                  lemmas_after = [];};
     "lb_find_preferred_available_backend", {
       ret_type = Static Sint32;
       arg_types = stt [Uint64;
                        Ptr vector_struct;
                        Ptr dchain_struct;
                        Uint32;
                        Uint32;
                        Ptr Sint32];
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
                 lemmas_after = [(fun params -> "a_packet_received = true;\n" ^
                                       let arg0 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn params.args 0) in
                                       simplify_c_string (
                                         "received_on_port = " ^
                                         "(*" ^ arg0 ^ ")->port;\n" ^
                                         "received_packet_type = " ^
                                         "(*" ^ arg0 ^ ")->packet_type;\n") ^
                                         (copy_stub_mbuf_content "pkt_recv"
                                          ("*" ^ arg0)));
                                 ];};
     "stub_core_trace_tx", {
                 ret_type = Static Uint8;
                 arg_types = stt [Ptr rte_mbuf_struct; Uint16];
                 extra_ptr_types = estt ["user_buf_addr",
                                         Ptr stub_mbuf_content_struct];
                 lemmas_before = [
                     (fun params ->
                          let sent_pkt = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn params.args 0) in
                            (copy_stub_mbuf_content "pkt_sent"
                             (sent_pkt)) ^ "\n" ^
                            simplify_c_string (
                              "sent_on_port = " ^ (List.nth_exn params.args 1) ^ ";\n" ^
                              "pkt_sent_type = (" ^
                              sent_pkt ^ ")->packet_type;"));];
                 lemmas_after = [(fun _ -> "a_packet_sent = true;\n");];
                 };
     "stub_core_trace_free", {
                   ret_type = Static Void;
                   arg_types = stt [Ptr rte_mbuf_struct;];
                   extra_ptr_types = estt ["user_buf_addr",
                                           Ptr stub_mbuf_content_struct];
                   lemmas_before = [];
                   lemmas_after = [];};
     "start_time", {ret_type = Static Sint64;
                    arg_types = [];
                    extra_ptr_types = [];
                    lemmas_before = [];
                    lemmas_after = [];};
     "vector_allocate", {ret_type = Static Sint32;
                         arg_types = stt [Sint32;
                                          Uint32;
                                          Fptr "vector_init_elem";
                                          Ptr (Ptr vector_struct)];
                         extra_ptr_types = [];
                         lemmas_before = [
                           tx_bl (* note that produce_function_pointer_chunk can only be done in an 'if', otherwise VeriFast complains *)
                              "if(!vector_flow_allocated) {\n\
                                produce_function_pointer_chunk vector_init_elem<lb_flowi>(lb_flow_init)\
                                (lb_flowp, sizeof(struct LoadBalancedFlow))(a) \
                                {\
                                call();\
                                }\n\
                              } else if(!vector_flow_id_to_bknd_id_allocated) {\n\
                                produce_function_pointer_chunk vector_init_elem<uint32_t>(null_init)\
                                (u_integer, sizeof(uint32_t))(a) \
                                {\
                                call();\
                                }\n\
                              } else if(!vector_backend_ips_allocated) {\n\
                                produce_function_pointer_chunk vector_init_elem<uint32_t>(null_init)\
                                (u_integer, sizeof(uint32_t))(a) \
                                {\
                                call();\
                                }\n\
                              } else if(!vector_backends_allocated) {\n\
                                produce_function_pointer_chunk vector_init_elem<lb_backendi>(lb_backend_init)\
                                (lb_backendp, sizeof(struct LoadBalancedBackend))(a) \
                                {\
                                call();\
                                }\n\
                              } else {\n\
                                produce_function_pointer_chunk vector_init_elem<uint32_t>(null_init)\
                                (u_integer, sizeof(uint32_t))(a) \
                                {\
                                call();\
                                }\n\
                              }\n";
                         ];
                         lemmas_after = [
                           (fun {tmp_gen;ret_name;_} ->
                              "/*@ if (" ^ ret_name ^
                              ") {\n\
                               if (!vector_flow_allocated) {\n\
                               assert mapp<lb_flowi>(_, _, _, _, mapc(?" ^ (tmp_gen "cap") ^
                              ", ?" ^ (tmp_gen "map") ^
                              ", ?" ^ (tmp_gen "addr_map") ^
                              "));\n\
                               assert vectorp<lb_flowi>(_, _, ?" ^ (tmp_gen "dks") ^
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
                              "if (!vector_flow_allocated) {\n\
                               vector_flow_allocated = true; } else {\n\
                               if (!vector_flow_id_to_bknd_id_allocated) {\n\
                               vector_flow_id_to_bknd_id_allocated = true; } else {\n\
                               if (!vector_backend_ips_allocated) {\n\
                               the_ip_vector = *" ^ (List.nth_exn args 3) ^
                              ";\n\
                               vector_backend_ips_allocated = true;\n\
                               } else {\n\
                               vector_backends_allocated = true;\n\
                               }}}");];};
     "lb_fill_cht",        {ret_type = Static Void;
                            arg_types = [Static (Ptr vector_struct);
                                         Static Sint32;
                                         Static Sint32];
                            extra_ptr_types = [];
                            lemmas_before = [];
                            lemmas_after = []};
     "vector_borrow",      {ret_type = Static Void;
                            arg_types = [Static (Ptr vector_struct);
                                         Static Sint32;
                                         Dynamic ["LoadBalancedFlow", Ptr (Ptr lb_flow_struct);
                                                  "LoadBalancedBackend", Ptr (Ptr lb_backend_struct);
                                                  "uint32_t", Ptr (Ptr Uint32)];];
                            extra_ptr_types = ["borrowed_cell",
                                               Dynamic ["LoadBalancedFlow", Ptr lb_flow_struct;
                                                        "LoadBalancedBackend", Ptr lb_backend_struct;
                                                        "uint32_t", Ptr Uint32];];
                            lemmas_before = [
                              (fun params ->
                                 match List.nth_exn params.arg_types 2 with
                                 | Ptr (Ptr (Str ("LoadBalancedFlow", _))) ->
                                   "/*@ if (!vector_backend_borrowed) { close hide_vector<lb_backendi>(_, _, _, _); } @*/\n" ^
                                   "//@ close hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ close hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ close hide_vector<uint32_t>(_, _, _, _);\n"
                                 | Ptr (Ptr (Str ("LoadBalancedBackend", _))) ->
                                   "/*@ if (!vector_flow_borrowed) { close hide_vector<lb_flowi>(_, _, _, _); } @*/\n" ^
                                   "/*@ { assert vectorp<lb_backendi>(_, _, ?" ^ (params.tmp_gen "vec") ^ ", _);\n\
                                          forall_mem(nth(" ^ (List.nth_exn params.args 1) ^ ", " ^ (params.tmp_gen "vec") ^ "), " ^ (params.tmp_gen "vec") ^ ", is_one);\n } @*/\n" ^
                                   "//@ close hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ close hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ close hide_vector<uint32_t>(_, _, _, _);\n"
                                 | Ptr (Ptr Uint32) ->
                                   "//@ close hide_vector<lb_backendi>(_, _, _, _);\n" ^
                                   "/*@ { assert vectorp<uint32_t>(" ^ (List.nth_exn params.args 0) ^ ", _, ?" ^
                                   (params.tmp_gen "vec") ^
                                   ", _);\n\
                                    if (forall(" ^ (params.tmp_gen "vec") ^
                                   ", is_one)) {\n\
                                    forall_mem(nth(" ^ (List.nth_exn params.args 1) ^ ", " ^ (params.tmp_gen "vec") ^ "), " ^ (params.tmp_gen "vec") ^ ", is_one);\n }\n}\n @*/\n"
                                 | _ ->
                                   failwith "Unsupported type for vector!")
                            ];
                            lemmas_after = [
                              (fun params ->
                                 match List.nth_exn params.arg_types 2 with
                                 | Ptr (Ptr (Str ("LoadBalancedFlow", _))) ->
                                   "/*@ if (!vector_backend_borrowed) { open hide_vector<lb_backendi>(_, _, _, _); } @*/\n" ^
                                   "vector_flow_borrowed = true;\n" ^
                                   "//@ open hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ open hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ open hide_vector<uint32_t>(_, _, _, _);\n"
                                 | Ptr (Ptr (Str ("LoadBalancedBackend", _))) ->
                                   "/*@ if (!vector_flow_borrowed) { open hide_vector<lb_flowi>(_, _, _, _); } @*/\n" ^
                                   "vector_backend_borrowed = true; \n" ^
                                   "//@ open hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ open hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ open hide_vector<uint32_t>(_, _, _, _);\n"
                                 | Ptr (Ptr Uint32) ->
                                   "//@ open hide_vector<lb_backendi>(_, _, _, _);\n"
                                 | _ ->
                                   failwith "Unsupported type for vector!")
                            ];};
     "vector_return",      {ret_type = Static Void;
                            arg_types = [Static (Ptr vector_struct);
                                         Static Sint32;
                                         Dynamic ["LoadBalancedFlow", Ptr lb_flow_struct;
                                                  "LoadBalancedBackend", Ptr lb_backend_struct;
                                                  "uint32_t", Ptr Uint32];];
                            extra_ptr_types = [];
                            lemmas_before = [
                              (fun params ->
                                 match List.nth_exn params.arg_types 2 with
                                 | Ptr (Str ("LoadBalancedFlow", _)) -> (* see remark in return_full *)
                                   "/*@ { assert vector_accp<lb_flowi>(_, _, ?" ^ (params.tmp_gen "vec") ^ ", _, _, _); \n\
                                          update_id(" ^ (List.nth_exn params.args 1) ^ ", " ^ (params.tmp_gen "vec") ^ "); } @*/"
                                 | Ptr (Str ("LoadBalancedBackend", _)) ->
                                   "/*@ { assert vector_accp<lb_backendi>(_, _, ?" ^ (params.tmp_gen "vec") ^
                                   ", _, _, _); \n\
                                    assert *&" ^
                                   (Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn params.args 2)) ^
                                   " |-> ? " ^ (params.tmp_gen "bknd") ^
                                   ";\n\
                                    assert lb_backendp(" ^
                                   (params.tmp_gen "bknd") ^
                                   ", ?" ^ (params.tmp_gen "bknd_logical") ^
                                   ");\n\
                                    forall_update<pair<lb_backendi, real> >(" ^ (params.tmp_gen "vec") ^
                                   ", is_one, " ^ (List.nth_exn params.args 1) ^
                                   ", pair(" ^ (params.tmp_gen "bknd_logical") ^
                                   ", 1.0));\n\
                                    update_id(" ^ (List.nth_exn params.args 1) ^ ", " ^ (params.tmp_gen "vec") ^ "); } @*/"
                                 | Ptr Uint32 -> ""
                                 | _ ->
                                   failwith "Unsupported type for vector!");
                              (fun params ->
                                 match List.nth_exn params.arg_types 2 with
                                 | Ptr (Str ("LoadBalancedFlow", _)) ->
                                   "/*@ if (vector_backend_borrowed) { close hide_vector_acc<lb_backendi>(_, _, _, _, _, _); } @*/\n"
                                 | Ptr (Str ("LoadBalancedBackend", _)) ->
                                   "/*@ if (vector_flow_borrowed) { close hide_vector_acc<lb_flowi>(_, _, _, _, _, _); } @*/\n"
                                 | Ptr Uint32 -> ""
                                 | _ ->
                                   failwith "Unsupported type for vector!")
                            ];
                            lemmas_after = [
                              (fun params ->
                                 match List.nth_exn params.arg_types 2 with
                                 | Ptr (Str ("LoadBalancedFlow", _)) ->
                                   "/*@ if (vector_backend_borrowed) { open hide_vector_acc<lb_backendi>(_, _, _, _, _, _); } @*/\n" ^
                                   "vector_flow_borrowed = false;"
                                 | Ptr (Str ("LoadBalancedBackend", _)) ->
                                   "/*@ if (vector_flow_borrowed) { open hide_vector_acc<lb_flowi>(_, _, _, _, _, _); } @*/\n" ^
                                   "vector_backend_borrowed = false;"
                                 | Ptr Uint32 -> ""
                                 | _ ->
                                   failwith "Unsupported type for vector!")
                            ];};]

module Iface : Fspec_api.Spec =
struct
  let preamble = "\
#include \"lib/expirator.h\"\n\
#include \"lib/stubs/time_stub_control.h\"\n\
#include \"lib/containers/map.h\"\n\
#include \"lib/containers/double-chain.h\"\n\
#include \"vigbalancer/lb_abstract.h\"\n\
#include \"vigbalancer/lb_loop.h\"\n\
#include \"vigbalancer/lb_balancer.h\"\n" ^
                 (In_channel.read_all "preamble.tmpl") ^
                 (In_channel.read_all "preamble_hide.tmpl") ^
                 "void to_verify()\n\
                  /*@ requires true; @*/ \n\
                  /*@ ensures true; @*/\n{\n\
                  //@ modulo_hack();\n\
                  uint16_t received_on_port;\n\
                  uint32_t received_packet_type;\n\
                  struct stub_mbuf_content pkt_recv;\n\
                  int the_index_allocated = -1;\n\
                  int64_t time_for_allocated_index = 0;\n\
                  bool a_packet_received = false;\n\
                  struct stub_mbuf_content pkt_sent;\n\
                  uint16_t sent_on_port;\n\
                  uint32_t pkt_sent_type;\n\
                  bool a_packet_sent = false;\n\
                  bool backend_known = false;\n\
                  struct Vector* the_ip_vector;\n\
                  int32_t backend_index = -1;\n"
                 ^ "//@ mapi<lb_flowi> initial_indices;\n"
                 ^ "//@ list<pair<lb_flowi, real> > initial_heap;\n"
                 ^ "//@ list<pair<lb_backendi, real> > initial_backends;\n"
                 ^ "//@ dchain initial_chain;\n"
                 ^ "//@ mapi<lb_flowi> expired_indices;\n"
                 ^ "//@ list<pair<lb_flowi, real> > expired_heap;\n"
                 ^ "//@ list<pair<lb_backendi, real> > expired_backends;\n"
                 ^ "//@ dchain expired_chain;\n"
                 ^ (* NOTE: looks like verifast pads the last uint8 of Flow with 3 bytes to 4-byte-align it... also TODO having to assume this is silly *)
                 "/*@ assume(sizeof(struct LoadBalancedFlow) == 16); @*/\n"
                 ^ "/*@ assume(sizeof(struct LoadBalancedBackend) == 12); @*/\n"
                 ^ "bool vector_flow_allocated = false;\n\
                    bool vector_flow_id_to_bknd_id_allocated = false;\n\
                    bool vector_backend_ips_allocated = false;\n\
                    bool vector_backends_allocated = false;\n\
                    bool map_flow_allocated = false;\n\
                    bool dchain_flow_allocated = false;\n\
                    bool map_flow_expired = false;\n\
                    bool last_map_accessed_lb_flowi = false;\n\
                    bool vector_flow_borrowed = false;\n\
                    bool vector_backend_borrowed = false;\n"
  let fun_types = fun_types
  let boundary_fun = "lb_loop_invariant_produce"
  let finishing_fun = "lb_loop_invariant_consume"
  let eventproc_iteration_begin = "lb_loop_invariant_produce"
  let eventproc_iteration_end = "lb_loop_invariant_consume"
  let user_check_for_complete_iteration = "" (* TODO: In_channel.read_all "lb_forwarding_property.tmpl" *)
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

