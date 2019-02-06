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

let hide_the_other_mapp {arg_types;tmp_gen;_} =
  match List.nth_exn arg_types 1 with
  | Ptr (Str ("ether_addr", _)) ->
    "//@ assert mapp<StaticKeyi>(?" ^ (tmp_gen "stm_ptr") ^
    ", _, _, _, ?" ^ (tmp_gen "stm") ^ ");\n\
                                        //@ close hide_mapp<StaticKeyi>(" ^
    (tmp_gen "stm_ptr") ^
    ", StaticKeyp, _StaticKey_hash, _," ^
    (tmp_gen "stm") ^ ");\n"
  | Ptr (Str ("StaticKey", _)) ->
    "//@ assert mapp<ether_addri>(?" ^ (tmp_gen "eam_ptr") ^
    ", _, _, _, ?" ^ (tmp_gen "dym") ^ ");\n\
                                        //@ close hide_mapp<ether_addri>(" ^
    (tmp_gen "eam_ptr") ^
    ", ether_addrp, _ether_addr_hash, _, " ^
    (tmp_gen "dym") ^
    ");\n"
  | _ -> "#error unexpected key type"

let reveal_the_other_mapp : lemma = fun {arg_types;tmp_gen;_} ->
  match List.nth_exn arg_types 1 with
  | Ptr (Str ("ether_addr", _)) ->
    "//@ open hide_mapp<StaticKeyi>(" ^
    (tmp_gen "stm_ptr") ^ ", StaticKeyp, _StaticKey_hash, _," ^
    (tmp_gen "stm") ^ ");\n"
  | Ptr (Str ("StaticKey", _)) ->
    "//@ open hide_mapp<ether_addri>(" ^
    (tmp_gen "eam_ptr") ^ ", ether_addrp, _ether_addr_hash, _," ^
    (tmp_gen "dym") ^ ");"
  | _ -> "#error unexpected key type"

let mempool_struct = Ir.Str ("rte_mempool", [])
let map_struct = Ir.Str ("Map", [])
let vector_struct = Ir.Str ( "Vector", [] )
let dchain_struct = Ir.Str ( "DoubleChain", [] )
let ether_addr_struct = Ir.Str ( "ether_addr", ["addr_bytes", Array Uint8;])
let static_key_struct = Ir.Str ( "StaticKey", ["addr", ether_addr_struct;
                                               "device", Uint16] )
let dynamic_value_struct = Ir.Str ( "DynamicValue", ["device", Uint16] )
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
let tcpudp_hdr_struct = Ir.Str ("tcpudp_hdr", ["src_port", Uint16;
                                               "dst_port", Uint16])
(* FIXME: for bridge only ether_hdr is needed, the other two are here,
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
                           "int64_t now = " ^ (params.ret_name) ^ ";\n");];};
     "ether_addr_hash", {ret_type = Static Uint32;
                         arg_types = stt [Ptr ether_addr_struct];
                         extra_ptr_types = [];
                         lemmas_before = [];
                         lemmas_after = [
                           (fun {args;_} ->
                              "//@ open ether_addrp(" ^ (List.nth_exn args 0) ^ ", _);\n")];};
     "bridge_loop_invariant_consume", {ret_type = Static Void;
                                       arg_types = stt
                                           [Ptr (Ptr dchain_struct);
                                            Ptr (Ptr map_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr map_struct);
                                            Ptr (Ptr vector_struct);
                                            Uint32;
                                            Sint64;
                                            Uint16];
                                       extra_ptr_types = [];
                                       lemmas_before = [
                                         (fun {args;_} ->
                                            "/*@ close bridge_loop_invariant(*" ^
                                            (List.nth_exn args 0) ^ ", *" ^
                                            (List.nth_exn args 1) ^ ", *" ^
                                            (List.nth_exn args 2) ^ ", *" ^
                                            (List.nth_exn args 3) ^ ", *" ^
                                            (List.nth_exn args 4) ^ ", *" ^
                                            (List.nth_exn args 5) ^ ", " ^
                                            (List.nth_exn args 6) ^ ", " ^
                                            (List.nth_exn args 7) ^ ", " ^
                                            (List.nth_exn args 8) ^ "); @*/");];
                                       lemmas_after = [];};
     "bridge_loop_invariant_produce", {ret_type = Static Void;
                                       arg_types = stt
                                           [Ptr (Ptr dchain_struct);
                                            Ptr (Ptr map_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr map_struct);
                                            Ptr (Ptr vector_struct);
                                            Uint32;
                                            Ptr Sint64;
                                            Uint16];
                                       extra_ptr_types = [];
                                       lemmas_before = [];
                                       lemmas_after = [
                                         (fun {args;_} ->
                                            "/*@ open bridge_loop_invariant (*" ^
                                            (List.nth_exn args 0) ^ ", *" ^
                                            (List.nth_exn args 1) ^ ", *" ^
                                            (List.nth_exn args 2) ^ ", *" ^
                                            (List.nth_exn args 3) ^ ", *" ^
                                            (List.nth_exn args 4) ^ ", *" ^
                                            (List.nth_exn args 5) ^ ", " ^
                                            (List.nth_exn args 6) ^ ", *" ^
                                            (List.nth_exn args 7) ^ ", " ^
                                            (List.nth_exn args 8) ^ "); @*/");
                                         (fun {tmp_gen;_} ->
                                            "\n/*@ {\n\
                                             assert mapp<ether_addri>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "dm") ^
                                            ", _));\n\
                                             assert vectorp<ether_addri>(_, _, ?" ^ (tmp_gen "dv") ^
                                            ", _);\n\
                                             assert vectorp<DynamicValuei>(_, _, ?" ^ (tmp_gen "dv_init") ^
                                            ", _);\n\
                                             assert vectorp<StaticKeyi>(_, _, ?" ^ (tmp_gen "sv") ^
                                            ", _);\n\
                                             assert map_vec_chain_coherent<ether_addri>(" ^
                                            (tmp_gen "dm") ^ ", " ^
                                            (tmp_gen "dv") ^ ", ?" ^
                                            (tmp_gen "dh") ^
                                            ");\n\
                                             mvc_coherent_same_len<ether_addri>(" ^ (tmp_gen "dm") ^
                                            ", " ^ (tmp_gen "dv") ^
                                            ", " ^ (tmp_gen "dh") ^
                                            ");\n\
                                             assert mapp<StaticKeyi>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "sm") ^
                                            ", _));\n\
                                            initial_dyn_map = " ^ (tmp_gen "dm") ^
                                            ";\ninitial_dyn_val_vec = " ^ (tmp_gen "dv_init") ^
                                            ";\ninitial_dyn_key_vec = " ^ (tmp_gen "dv") ^
                                            ";\ninitial_chain = " ^ (tmp_gen "dh") ^
                                            ";\ninitial_stat_map = " ^ (tmp_gen "sm") ^
                                            ";\ninitial_stat_key_vec = " ^ (tmp_gen "sv") ^
                                            ";\n} @*/");
                                       ];};
     "dchain_allocate", {ret_type = Static Sint32;
                         arg_types = stt [Sint32; Ptr (Ptr dchain_struct)];
                         extra_ptr_types = [];
                         lemmas_before = [];
                         lemmas_after = [
                           on_rez_nonzero
                             "{\n\
                              assert vectorp<ether_addri>(_, _, ?allocated_vector, _);\n\
                              empty_map_vec_dchain_coherent\
                              <ether_addri>(allocated_vector);\n\
                              }";
                           tx_l "index_range_of_empty(65536, 0);";];};
     "dchain_allocate_new_index", {ret_type = Static Sint32;
                                   arg_types = stt [Ptr dchain_struct; Ptr Sint32; vigor_time_t;];
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
                                          (List.nth_exn params.args 2) ^
                                          ");\n\
                                           dchain_indexes_contain_index(" ^
                                          (params.tmp_gen "cur_ch") ^
                                          ", *" ^
                                          (List.nth_exn params.args 1) ^
                                          ");\n}");
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
                                          "{\n\
                                           assert map_vec_chain_coherent<\
                                           ether_addri>(?" ^
                                          (tmp_gen "cur_map") ^ ", ?" ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^
                                          ");\n\
                                           mvc_coherent_alloc_is_halfowned<ether_addri>(" ^
                                          (tmp_gen "cur_map") ^ ", " ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^ ", *" ^
                                          (List.nth_exn args 1) ^ ");\n}");
                                   ];};
     "dchain_rejuvenate_index", {ret_type = Static Sint32;
                                 arg_types = stt [Ptr dchain_struct;
                                                  Sint32; vigor_time_t;];
                                 extra_ptr_types = [];
                                 lemmas_before = [
                                   capture_chain "cur_ch" 0;
                                   (fun {tmp_gen;_} ->
                                      "/*@ {\n\
                                        assert map_vec_chain_coherent<\
                                       ether_addri>(?" ^
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
                                      "assert map_vec_chain_coherent<ether_addri>\
                                       (?cur_map,?cur_vec,?cur_ch);\n" ^
                                      "mvc_rejuvenate_preserves_coherent(cur_map,\
                                       cur_vec, cur_ch, " ^
                                      (List.nth_exn params.args 1) ^ ", "
                                      ^ (List.nth_exn params.args 2) ^ ");\n\
                                       rejuvenate_preserves_index_range(cur_ch," ^
                                      (List.nth_exn params.args 1) ^ ", " ^
                                      (List.nth_exn params.args 2) ^ ");\n}@*/");
                                   (fun params ->
                                      "int the_index_rejuvenated = " ^
                                      (List.nth_exn params.args 1) ^ ";\n");
                                 ];};
     "expire_items_single_map", {ret_type = Static Sint32;
                                 arg_types = stt [Ptr dchain_struct;
                                                  Ptr vector_struct;
                                                  Ptr map_struct;
                                                  vigor_time_t];
                                 extra_ptr_types = [];
                                 lemmas_before = [
                                   (fun {tmp_gen;_} ->
                                      "//@ assert mapp<StaticKeyi>(?" ^
                                      (tmp_gen "stmp") ^ ", _, _, _, ?stm);\n" ^
                                      "//@ close hide_mapp<StaticKeyi>(" ^
                                      (tmp_gen "stmp") ^ ", StaticKeyp,\
                                                          _StaticKey_hash,\
                                                          _,\
                                                          stm);\n");
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
                                      "//@ open hide_mapp<StaticKeyi>(" ^
                                      (tmp_gen "stmp") ^ ", StaticKeyp,\
                                                          _StaticKey_hash,\
                                                          _,\
                                                          stm);\n");
                                   (fun {tmp_gen;_} ->
                                      "\n/*@ {\n\
                                       assert mapp<ether_addri>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "dm") ^
                                      ", _));\n\
                                       assert vectorp<ether_addri>(_, _, ?" ^ (tmp_gen "dv") ^
                                      ", _);\n\
                                       assert map_vec_chain_coherent<ether_addri>(" ^
                                      (tmp_gen "dm") ^ ", " ^
                                      (tmp_gen "dv") ^ ", ?" ^
                                      (tmp_gen "dh") ^
                                      ");\n\
                                       mvc_coherent_same_len<ether_addri>(" ^
                                      (tmp_gen "dm") ^ ", " ^
                                      (tmp_gen "dv") ^ ", " ^
                                      (tmp_gen "dh") ^
                                      ");\nmvc_coherent_distinct<ether_addri>(" ^
                                      (tmp_gen "dm") ^ ", " ^
                                      (tmp_gen "dv") ^ ", " ^
                                      (tmp_gen "dh") ^
                                      ");\n} @*/"
                                         );
                                 ];};
     "map_allocate", {ret_type = Static Sint32;
                      arg_types = stt [Fptr "map_keys_equality";
                                       Fptr "map_key_hash";
                                       Uint32;
                                       Ptr (Ptr map_struct)];
                      extra_ptr_types = [];
                      lemmas_before = [
                        (fun {args;_} ->
                           "/*@ if (" ^ (List.nth_exn args 0) ^
                           " == StaticKey_eq) {\n" ^
                           "produce_function_pointer_chunk \
                            map_keys_equality<StaticKeyi>(StaticKey_eq)\
                            (StaticKeyp)(a, b) \
                            {\
                            call();\
                            }\n\
                            produce_function_pointer_chunk \
                            map_key_hash<StaticKeyi>(StaticKey_hash)\
                            (StaticKeyp, _StaticKey_hash)(a) \
                            {\
                            call();\
                            }\n\
                            } else {\n\
                            produce_function_pointer_chunk \
                            map_keys_equality<ether_addri>(ether_addr_eq)\
                            (ether_addrp)(a, b) \
                            {\
                            call();\
                            }\n\
                            produce_function_pointer_chunk \
                            map_key_hash<ether_addri>(ether_addr_hash)\
                            (ether_addrp, _ether_addr_hash)(a) \
                            {\
                            call();\
                            }\n\
                            } @*/ \n");];
                      lemmas_after = [
                        (fun params ->
                           "/*@ if (" ^ (List.nth_exn params.args 0) ^
                           " == StaticKey_eq) {\n\
                            assert [?" ^ (params.tmp_gen "imkest") ^
                           "]is_map_keys_equality(StaticKey_eq,\
                            StaticKeyp);\n\
                            close [" ^ (params.tmp_gen "imkest") ^
                           "]hide_is_map_keys_equality(StaticKey_eq, \
                            StaticKeyp);\n\
                            assert [?" ^ (params.tmp_gen "imkhst") ^
                           "]is_map_key_hash(StaticKey_hash,\
                            StaticKeyp, _StaticKey_hash);\n\
                            close [" ^ (params.tmp_gen "imkhst") ^
                           "]hide_is_map_key_hash(StaticKey_hash, \
                            StaticKeyp, _StaticKey_hash);\n\
                            } else {\n\
                            assert [?" ^ (params.tmp_gen "imkedy") ^
                           "]is_map_keys_equality(ether_addr_eq,\
                            ether_addrp);\n\
                            close [" ^ (params.tmp_gen "imkedy") ^
                           "]hide_is_map_keys_equality(ether_addr_eq, \
                            ether_addrp);\n\
                            assert [?" ^ (params.tmp_gen "imkhdy") ^
                           "]is_map_key_hash(ether_addr_hash,\
                            ether_addrp, _ether_addr_hash);\n\
                            close [" ^ (params.tmp_gen "imkhdy") ^
                           "]hide_is_map_key_hash(ether_addr_hash, \
                            ether_addrp, _ether_addr_hash);\n\
                            } @*/")];};
     "map_get", {ret_type = Static Sint32;
                 arg_types = [Static (Ptr map_struct);
                              Dynamic ["ether_addr", Ptr ether_addr_struct;
                                       "StaticKey", Ptr static_key_struct];
                              Static (Ptr Sint32)];
                 extra_ptr_types = [];
                 lemmas_before = [
                   hide_the_other_mapp;
                   (fun ({arg_types;tmp_gen;arg_exps;_} as params) ->
                      match List.nth_exn arg_types 1 with
                      | Ptr (Str ("ether_addr", _)) ->
                        let (binding,expr) =
                          self_dereference (List.nth_exn arg_exps 1) tmp_gen
                        in
                        binding ^
                        "\n" ^
                        "//@ assert ether_addrp(" ^ (render_tterm expr) ^ ", ?" ^ (tmp_gen "dk") ^ ");\n" ^
                        (capture_a_chain "dh" params ^
                         capture_a_map "ether_addri" "dm" params ^
                         capture_a_vector "ether_addri" "dv" params);
                      | Ptr (Str ("StaticKey", _)) ->
                        (capture_a_map "StaticKeyi" "stm" params) ^
                        "//@ assert uchars((" ^ (render_tterm (List.nth_exn arg_exps 1)) ^
                        ")->addr.addr_bytes, 6, ?" ^ (tmp_gen "sk") ^ ");\n" ^
                        "//@ list_of_six(" ^ (tmp_gen "sk") ^ ");\n"
                      | _ -> "#error unexpected key type")];
                 lemmas_after = [
                   reveal_the_other_mapp;
                   (fun {args;ret_name;arg_types;tmp_gen;arg_exps;_} ->
                      match List.nth_exn arg_types 1 with
                      | Ptr (Str ("ether_addr", _)) ->
                        let (binding,expr) =
                          self_dereference (List.nth_exn arg_exps 1) tmp_gen
                        in
                        "//@ open [_]ether_addrp(" ^ (render_tterm expr) ^ ", " ^ (tmp_gen "dk") ^ ");\n" ^
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
                         } @*/"
                      | Ptr (Str ("StaticKey", _)) ->
                        "/*@ if (" ^ ret_name ^
                        " != 0) {\n\
                         assert StaticKeyp(" ^ (List.nth_exn args 1) ^
                        ", ?stkey);\n\
                         map_get_mem(" ^ (tmp_gen "stm") ^
                        ", stkey);\n\
                         forall_mem(pair(stkey, *" ^ (List.nth_exn args 2) ^
                        "), " ^ (tmp_gen "stm") ^
                        ", (st_entry_bound)(2));\n\
                         } @*/\n" ^
                        "//@ open StaticKeyp(" ^ (List.nth_exn args 1) ^ ", _);\n" ^
                        "//@ open ether_addrp(" ^ (List.nth_exn args 1) ^ ".addr, _);\n"
                      | _ -> "");];};
     "map_put", {ret_type = Static Void;
                 arg_types = [Static (Ptr map_struct);
                              Dynamic ["ether_addr", Ptr ether_addr_struct;
                                       "StaticKey", Ptr static_key_struct];
                              Static Sint32];
                 extra_ptr_types = [];
                 lemmas_before = [
                   (fun {tmp_gen;_} ->
                       "\n//@ assert mapp<ether_addri>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "dm") ^
                       ", _));\n");
                   (fun {tmp_gen;_} ->
                      "\n/*@ {\n\
                       assert map_vec_chain_coherent<ether_addri>(" ^
                      (tmp_gen "dm") ^ ", ?" ^
                      (tmp_gen "dv") ^ ", ?" ^
                      (tmp_gen "dh") ^
                      ");\n\
                       mvc_coherent_dchain_non_out_of_space_map_nonfull<ether_addri>(" ^
                      (tmp_gen "dm") ^ ", " ^
                      (tmp_gen "dv") ^ ", " ^
                      (tmp_gen "dh") ^ ");\n} @*/");
                   (fun {args;_} ->
                      let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
                   arg1 ^ "bis = " ^ arg1 ^ ";\n" ^
                   "/*@ { \n\
                    assert mapp<ether_addri>(_, _, _, _, mapc(_, ?the_dm, ?dm_addrs)); \n\
                    assert vectorp<ether_addri>(_, _, _, ?dv_addrs); \n\
                    assert map_vec_chain_coherent<ether_addri>(the_dm, ?the_dv, ?the_dh);\n\
                    assert ether_addrp(" ^ arg1 ^ "bis->addr_bytes, ?vvv);\n\
                    mvc_coherent_key_abscent(the_dm, the_dv, the_dh, vvv);\n\
                    kkeeper_add_one(dv_addrs, the_dv, dm_addrs, vvv, " ^ (List.nth_exn args 2) ^ "); \n\
                    } @*/");
                   hide_the_other_mapp];
                 lemmas_after = [
                   (fun {tmp_gen;args;_} -> let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
                      arg1 ^ "bis = " ^ arg1 ^ ";\n" ^ 
                      "/*@ {\n\
                       assert map_vec_chain_coherent<ether_addri>(" ^ (tmp_gen "dm") ^
                      ", ?" ^ (tmp_gen "dv") ^
                      ", ?" ^ (tmp_gen "dh") ^
                      ");\n\
                       assert [?" ^ (tmp_gen "fr") ^ "]ether_addrp(" ^ arg1 ^ "bis, ?" ^ (tmp_gen "ea") ^ ");\n\
                       mvc_coherent_put<ether_addri>(" ^ (tmp_gen "dm") ^
                      ", " ^ (tmp_gen "dv") ^
                      ", " ^ (tmp_gen "dh") ^
                      ", " ^ (List.nth_exn args 2) ^
                      ", time_for_allocated_index, " ^ (tmp_gen "ea") ^ ");\n\
                      open [" ^ (tmp_gen "fr") ^ "]ether_addrp(" ^ arg1 ^ "bis, " ^ (tmp_gen "ea") ^ ");\n\
                       } @*/"
                   );
                   reveal_the_other_mapp];};
     "packet_receive", {ret_type = Static Boolean;
                        arg_types = stt [Uint16; Ptr (Ptr Sint8); Ptr Uint16];
                        extra_ptr_types = [];
                        lemmas_before = [];
                        lemmas_after = [
                          (fun {args;ret_name;_} ->
                             "a_packet_received = " ^ ret_name ^ " ;\n" ^
                             "received_on_port = " ^ (List.nth_exn args 0) ^ ";\n"
                          )
                        ];};
     "packet_send", {ret_type = Static Void;
                     arg_types = stt [Ptr Sint8; Uint16];
                     extra_ptr_types = [];
                     lemmas_before = [(fun {arg_exps;tmp_gen;_} ->
                         let packet_ptr = (render_tterm (List.nth_exn arg_exps 0)) in
                         "char* " ^ (tmp_gen "synonym") ^ " = " ^ packet_ptr ^
                         ";\n/*@ {\n\ assert packetp(" ^ (tmp_gen "synonym") ^
                         ", ?cur_sent_packet, nil);\n\
                          if (last_sent_packet == nil) { \n\
                          assert packet_is_complete;\n\
                          switch(last_composed_packet) {\n\
                          case none: assert false;\n\
                          case some(cp): assert packetp(cp, cur_sent_packet, nil);\n\
                          }\n\
                          last_sent_packet = cur_sent_packet;\n\
                          } else {\n\
                          assert last_sent_packet == cur_sent_packet;\n\
                          }\n }\n @*/"
                       )];
                     lemmas_after = [
                       (fun {args;_} ->
                         "sent_on_ports = cons(" ^ (List.nth_exn args 1) ^ ", sent_on_ports);\n" 
                       )];};
     "packet_borrow_next_chunk", {ret_type = Static Void;
                                  arg_types = [Static (Ptr Sint8);
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
                                  lemmas_before = [(fun _ -> "//@ packet_is_complete = false;")];
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
                             arg_types = [Static (Ptr Sint8);
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
                                    "->s_addr), _);\n\
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
                             lemmas_after = [
                               (fun {arg_exps;tmp_gen;_} ->
                                  let packet_ptr = (render_tterm (List.nth_exn arg_exps 0)) in
                                  "char* " ^ (tmp_gen "synonym") ^ " = " ^ packet_ptr ^
                                  ";\n/*@ {\n assert packetp(" ^ (tmp_gen "synonym") ^
                                  ", _, ?unreturned_chunks);\n\
                                   switch(last_composed_packet) {\n\
                                   case none:\n\
                                   last_composed_packet = some(" ^ packet_ptr ^
                                  ");\n\
                                   case some(cp):\n\
                                   assert cp == " ^ packet_ptr ^
                                  ";\n};\n\
                                  packet_is_complete = (unreturned_chunks == nil);\n \
                                   }\n@*/"
                               )];};
     "packet_get_unread_length", {ret_type = Static Uint32;
                                  arg_types = stt [Ptr Sint8];
                                  extra_ptr_types = [];
                                  lemmas_before = [];
                                  lemmas_after = [];};
     "packet_state_total_length", {ret_type = Static Void;
                                   arg_types = stt [Ptr Sint8;
                                                    Ptr Uint16];
                                   extra_ptr_types = [];
                                   lemmas_before = [];
                                   lemmas_after = [];};
     "packet_free", {ret_type = Static Void;
                     arg_types = stt [Ptr Sint8;];
                     extra_ptr_types = [];
                     lemmas_before = [];
                     lemmas_after = [];};
     "packet_clone", {ret_type = Static Void;
                      arg_types = stt [Ptr Sint8;
                                       Ptr (Ptr Sint8)];
                      extra_ptr_types = [];
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
                           tx_bl
                             "if (stat_vec_allocated) {\n\
                              if (dyn_keys_allocated) {\n\
                              produce_function_pointer_chunk \
                              vector_init_elem<DynamicValuei>(DynamicValue_allocate)\
                              (DynamicValuep, sizeof(struct DynamicValue))(a) \
                              {\
                              call();\
                              }\n\
                              } else {\n\
                              produce_function_pointer_chunk \
                              vector_init_elem<ether_addri>(ether_addr_allocate)\
                              (ether_addrp, sizeof(struct ether_addr))(a) \
                              {\
                              call();\
                              }\n\
                              }\n\
                              } else {\n\
                              produce_function_pointer_chunk \
                              vector_init_elem<StaticKeyi>(StaticKey_allocate)\
                              (StaticKeyp, sizeof(struct StaticKey))(a) \
                              {\
                              call();\
                              }\n\
                              }";
                         ];
                         lemmas_after = [
                           (fun {tmp_gen;ret_name;_} ->
                              "/*@ if (" ^ ret_name ^
                              " && stat_vec_allocated && !dyn_keys_allocated) {\n\
                               assert mapp<ether_addri>(_, _, _, _, mapc(?" ^ (tmp_gen "cap") ^
                              ", ?" ^ (tmp_gen "map") ^
                              ", ?" ^ (tmp_gen "addr_map") ^
                              "));\n\
                               assert vectorp<ether_addri>(_, _, ?" ^ (tmp_gen "dks") ^
                              ", ?" ^ (tmp_gen "dkaddrs") ^
                              ");\n\
                               empty_kkeeper(" ^
                              (tmp_gen "dkaddrs") ^
                              ", " ^ (tmp_gen "dks") ^
                              ", " ^ (tmp_gen "addr_map") ^
                              ", " ^ (tmp_gen "cap") ^ ");\n } @*/");
                           (fun _ ->
                              "if (!stat_vec_allocated)\
                               stat_vec_allocated = true;\n\
                               else if (!dyn_keys_allocated)\ dyn_keys_allocated = true;");];};
     "vector_borrow",      {ret_type = Static Void;
                            arg_types = [Static (Ptr vector_struct);
                                         Static Sint32;
                                         Dynamic ["StaticKey",
                                                  Ptr (Ptr static_key_struct);
                                                  "ether_addr",
                                                  Ptr (Ptr ether_addr_struct);
                                                  "DynamicValue",
                                                  Ptr (Ptr dynamic_value_struct)]];
                            extra_ptr_types = ["borrowed_cell",
                                               Dynamic ["StaticKey",
                                                        Ptr static_key_struct;
                                                        "ether_addr",
                                                        Ptr ether_addr_struct;
                                                        "DynamicValue",
                                                        Ptr dynamic_value_struct]];
                            lemmas_before = [
                              (fun {args;arg_types;tmp_gen;_} ->
                                 match List.nth_exn arg_types 2 with
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "StaticKey"->
                                   "/*@ {\n\
                                    close hide_vector<ether_addri>(_, _, _, _);\n\
                                    close hide_vector<DynamicValuei>(_, _, _, _);\n} @*/"
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "ether_addr"->
                                   "/*@ {\n\
                                    close hide_vector<StaticKeyi>(_, _, _, _);\n\
                                    close hide_vector<DynamicValuei>(_, _, _, _);\n} @*/\n"
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "DynamicValue"->
                                   "/*@ {\n\
                                    close hide_vector<StaticKeyi>(_, _, _, _);\n\
                                    close hide_vector<ether_addri>(_, _, _, _);\n\
                                    assert vectorp<DynamicValuei>(_, _, ?" ^ (tmp_gen "vec") ^ ", _);\n\
                                    forall_mem(nth(" ^ (List.nth_exn args 1) ^ ", " ^ (tmp_gen "vec") ^ "), " ^ (tmp_gen "vec") ^ ", is_one);\n} @*/"
                                 | x -> "Error: unexpected argument type: " ^ (ttype_to_str x))
                            ];
                            lemmas_after = [
                              (fun {arg_types;args;_} ->
                                 match List.nth_exn arg_types 2 with
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "StaticKey"->
                                   "/*@ {\n\
                                    open hide_vector<ether_addri>(_, _, _, _);\n\
                                    open hide_vector<DynamicValuei>(_, _, _, _);\n} @*/\n\
                                    stat_vec_borrowed = true;"
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "ether_addr"->
                                   "/*@ {\n\
                                    open hide_vector<StaticKeyi>(_, _, _, _);\n\
                                    open hide_vector<DynamicValuei>(_, _, _, _);\n} @*/\n\
                                    dyn_ks_borrowed = true;\n" ^
                                   "//@ open ether_addrp(*" ^ (List.nth_exn args 2) ^ ", _);\n"
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "DynamicValue"->
                                   "/*@ {\n\
                                    open hide_vector<StaticKeyi>(_, _, _, _);\n\
                                    open hide_vector<ether_addri>(_, _, _, _);\n} @*/\n\
                                    dyn_vs_borrowed = true;"
                                 | x -> "Error: unexpected argument type: " ^ (ttype_to_str x));
                              ];};
     "vector_return",      {ret_type = Static Void;
                            arg_types = [Static (Ptr vector_struct);
                                         Static Sint32;
                                         Dynamic ["StaticKey",
                                                  Ptr static_key_struct;
                                                  "ether_addr",
                                                  Ptr ether_addr_struct;
                                                  "DynamicValue",
                                                  Ptr dynamic_value_struct]];
                            extra_ptr_types = [];
                            lemmas_before = [
                              (fun {arg_types;tmp_gen;args;_} ->
                                 match List.nth_exn arg_types 2 with
                                 | Ptr (Str (name, _))
                                   when String.equal name "StaticKey" ->
                                   "\n/*@ { \n\
                                    assert vectorp<StaticKeyi>(_, _, ?vectr, _); \n\
                                    update_id(" ^ (List.nth_exn args 1) ^
                                   ", vectr);\n\
                                    assert StaticKeyp(" ^ (List.nth_exn args 2) ^
                                   ", ?the_key);\n\
                                    forall_update(vectr, is_one, " ^ (List.nth_exn args 1) ^
                                   ", pair(the_key, 1.0));\n\
                                    } @*/"
                                 | Ptr (Str (name, _))
                                   when String.equal name "ether_addr" ->
                                   "\n/*@ { \n\
                                    assert vectorp<ether_addri>(_, _, ?vectr, _); \n\
                                    update_id(" ^ (List.nth_exn args 1) ^
                                   ", vectr);\n\
                                      } @*/"
                                 | Ptr (Str (name, _))
                                   when String.equal name "DynamicValue"->
                                   "\n/*@ {\n\
                                    assert vectorp<DynamicValuei>(_, _, ?" ^ (tmp_gen "vec") ^
                                   ", _);\n\
                                    update_id(" ^ (List.nth_exn args 1) ^
                                   ", " ^ (tmp_gen "vec") ^ ");\n\
                                   } @*/\n"
                                 | x -> "Error: unexpected argument type: " ^ (ttype_to_str x));
                                (fun {arg_types;_} ->
                                   match List.nth_exn arg_types 2 with
                                   | Ptr (Str (name, _))
                                     when String.equal name "StaticKey" ->
                                     "/*@ {\n\
                                      close hide_vector<ether_addri>(_, _, _, _);\n\
                                      close hide_vector<DynamicValuei>(_, _, _, _);\n} @*/"
                                   | Ptr (Str (name, _))
                                     when String.equal name "ether_addr" ->
                                     "/*@ {\n\
                                      close hide_vector<StaticKeyi>(_, _, _, _);\n\
                                      close hide_vector<DynamicValuei>(_, _, _, _);\n} @*/"
                                   | Ptr (Str (name, _))
                                     when String.equal name "DynamicValue" ->
                                     "/*@ {\n\
                                      close hide_vector<ether_addri>(_, _, _, _);\n\
                                      close hide_vector<StaticKeyi>(_, _, _, _);\n} @*/"
                                   | x -> "Error: unexpected argument type: " ^ (ttype_to_str x));
                            ];
                            lemmas_after = [
                                (fun {arg_types;_} ->
                                   match List.nth_exn arg_types 2 with
                                   | Ptr (Str (name, _))
                                     when String.equal name "StaticKey" ->
                                     "/*@ {\n\
                                      open hide_vector<ether_addri>(_, _, _, _);\n\
                                      open hide_vector<DynamicValuei>(_, _, _, _);\n} @*/\n\
                                      stat_vec_borrowed = false;"
                                   | Ptr (Str (name, _))
                                     when String.equal name "ether_addr" ->
                                     "/*@ {\n\
                                      open hide_vector<StaticKeyi>(_, _, _, _);\n\
                                      open hide_vector<DynamicValuei>(_, _, _, _);\n} @*/\n\
                                      dyn_ks_borrowed = false;"
                                   | Ptr (Str (name, _))
                                     when String.equal name "DynamicValue" ->
                                     "/*@ {\n\
                                      open hide_vector<ether_addri>(_, _, _, _);\n\
                                      open hide_vector<StaticKeyi>(_, _, _, _);\n} @*/\n\
                                      dyn_vs_borrowed = false;"
                                   | x -> "Error: unexpected argument type: " ^ (ttype_to_str x));
                            ];};]

(* TODO: make external_ip symbolic *)
module Iface : Fspec_api.Spec =
struct
  let preamble = "\
#include \"lib/expirator.h\"\n\
#include \"lib/stubs/time_stub_control.h\"\n\
#include \"lib/containers/map.h\"\n\
#include \"lib/containers/double-chain.h\"\n\
#include \"vigbridge/bridge_loop.h\"\n" ^
                 (In_channel.read_all "preamble.tmpl") ^
                 (In_channel.read_all "preamble_hide.tmpl") ^
                 "void to_verify()\n\
                  /*@ requires true; @*/ \n\
                  /*@ ensures true; @*/\n{\n\
                  uint16_t received_on_port;\n\
                  int the_index_allocated = -1;\n\
                  int64_t time_for_allocated_index = 0;\n\
                  bool a_packet_received = false;\n\
                  bool is_ipv4 = false;\n\
                  //@ bool packet_is_complete = false;\n\
                  //@ option<void*> last_composed_packet = none;\n\
                  //@ list<uint8_t> last_sent_packet = nil;\n\
                  uint32_t sent_packet_type;\n"
                 ^ "//@ list<pair<ether_addri, int> > initial_dyn_map;\n"
                 ^ "//@ dchain initial_chain;\n"
                 ^ "//@ list<pair<DynamicValuei, real> > initial_dyn_val_vec;\n"
                 ^ "//@ list<pair<ether_addri, real> > initial_dyn_key_vec;\n"
                 ^ "//@ list<pair<StaticKeyi, int> > initial_stat_map;\n"
                 ^ "//@ list<pair<StaticKeyi, real> > initial_stat_key_vec;\n" ^
                 "//@ list<phdr> recv_headers = nil; \n\
                  //@ list<phdr> sent_headers = nil; \n\
                  //@ list<int> sent_on_ports = nil; \n"
                 ^
                 "/*@ //TODO: this hack should be \
                  converted to a system \n\
                  assume(sizeof(struct ether_addr) == 6);\n@*/\n\
                  //@ assume(sizeof(struct ether_hdr) == 14);\n\
                  /*@ assume(sizeof(struct DynamicValue) == 2);\n@*/\n\
                  /*@\
                  assume(sizeof(struct StaticKey) == 8);\n@*/\n"
                 ^
                 "/*@ assume(ether_addr_eq != StaticKey_eq); @*/\n"
                 ^
                 "bool stat_vec_allocated = false;\n"
                 ^
                 "bool dyn_keys_allocated = false;\n"
                 ^
                 "bool dyn_ks_borrowed = false;\n\
                  bool dyn_vs_borrowed = false;\n\
                  bool stat_vec_borrowed = false;\n"
  let fun_types = fun_types
  let boundary_fun = "bridge_loop_invariant_produce"
  let finishing_fun = "bridge_loop_invariant_consume"
  let eventproc_iteration_begin = "bridge_loop_invariant_produce"
  let eventproc_iteration_end = "bridge_loop_invariant_consume"
  let user_check_for_complete_iteration = In_channel.read_all "bridge_forwarding_property.tmpl"
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

