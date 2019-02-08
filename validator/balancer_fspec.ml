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

let mempool_struct = Ir.Str ("rte_mempool", [])
let map_struct = Ir.Str ("Map", [])
let vector_struct = Ir.Str ( "Vector", [] )
let dchain_struct = Ir.Str ( "DoubleChain", [] )

let ether_addr_struct = Ir.Str ( "ether_addr", ["addr_bytes", Array Uint8;])
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

let ip_addr_struct = Ir.Str("ip_addr", ["addr", Uint32])

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
     "LoadBalancedFlow_hash", {ret_type = Static Uint32;
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
                                            (List.nth_exn args 11) ^ ", " ^
                                            (List.nth_exn args 12) ^ "); @*/");];
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
                                            (List.nth_exn args 11) ^ ", " ^
                                            (List.nth_exn args 12) ^ "); @*/");
                                         (fun {tmp_gen;args;_} ->
                                            "\n/*@ {\n\
                                             assert mapp<LoadBalancedFlowi>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "fi") ^ ", _));\n\
                                             assert vectorp<LoadBalancedBackendi>(_, _, ?" ^ (tmp_gen "fb") ^ ", _);\n\
                                             assert map_vec_chain_coherent<LoadBalancedFlowi>(" ^
                                            (tmp_gen "fi") ^ ", ?" ^
                                            (tmp_gen "fh") ^ ", ?" ^
                                            (tmp_gen "ch") ^
                                            ");\n\
                                             mvc_coherent_same_len<LoadBalancedFlowi>(" ^ 
                                                   (tmp_gen "fi") ^
                                            ", " ^ (tmp_gen "fh") ^
                                            ", " ^ (tmp_gen "ch") ^
                                            ");\n\
                                             assert mapp<LoadBalancedFlowi>(_, _, _, _, ?" ^ (tmp_gen "fi_full") ^ ");\n" ^ 
                                            "assert mapp<LoadBalancedFlowi>(_ "^
                                            ", _, _, _, mapc(_, ?" ^ (tmp_gen "initial_flow_map") ^
                                            ", _));\n" ^
                                            "assert vectorp<LoadBalancedFlowi>(_" ^
                                            ", _, ?" ^ (tmp_gen "initial_flow_vec") ^
                                            ", _);\n" ^
                                            "assert *" ^ (List.nth_exn args 2) ^ " |-> ?" ^ (tmp_gen "arg2bis") ^
                                            ";\nassert double_chainp(?" ^ (tmp_gen "initial_flow_chain") ^
                                            ", " ^ (tmp_gen "arg2bis") ^
                                            ");\n" ^
                                            "assert *" ^ (List.nth_exn args 3) ^ " |-> ?" ^ (tmp_gen "arg3bis") ^
                                            ";\nassert vectorp<uint32_t>(" ^ (tmp_gen "arg3bis") ^
                                            ", _, ?" ^ (tmp_gen "initial_fidbid_veca") ^
                                            ", _);\n" ^
                                            "assert *" ^ (List.nth_exn args 4) ^ " |-> ?" ^ (tmp_gen "arg4bis") ^
                                            ";\nassert vectorp<ip_addri>(" ^ (tmp_gen "arg4bis") ^
                                            ", _, ?" ^ (tmp_gen "initial_ip_veca") ^
                                            ", _);\n" ^
                                            "assert *" ^ (List.nth_exn args 5) ^ " |-> ?" ^ (tmp_gen "arg5bis") ^
                                            ";\nassert vectorp<LoadBalancedBackendi>(" ^ (tmp_gen "arg5bis") ^
                                            ", _, ?" ^ (tmp_gen "initial_backends_veca") ^
                                            ", _);\n" ^
                                            "assert *" ^ (List.nth_exn args 6) ^ " |-> ?" ^ (tmp_gen "arg6bis") ^
                                            ";\nassert mapp<ip_addri>(" ^ (tmp_gen "arg6bis") ^
                                            ", _, _, _, mapc(_, ?" ^ (tmp_gen "initial_backend_ip_map") ^
                                            ", _));\n" ^
                                            "assert *" ^ (List.nth_exn args 7) ^ " |-> ?" ^ (tmp_gen "arg7bis") ^
                                            ";\nassert double_chainp(?" ^ (tmp_gen "initial_active_backends") ^
                                            ", " ^ (tmp_gen "arg7bis") ^
                                            ");\n" ^
                                            "assert *" ^ (List.nth_exn args 8) ^ " |-> ?" ^ (tmp_gen "arg8bis") ^
                                            ";\nassert vectorp<uint32_t>(" ^ (tmp_gen "arg8bis") ^
                                            ", _, ?" ^ (tmp_gen "initial_cht") ^
                                            ", _);\n" ^
                                            ";\nfidbid_veca_ptr = " ^ (tmp_gen "arg3bis") ^
                                            ";\nbackends_veca_ptr = " ^ (tmp_gen "arg5bis") ^
                                            ";\ncht_ptr = " ^ (tmp_gen "arg8bis") ^
                                            ";\nflow_map = " ^ (tmp_gen "initial_flow_map") ^
                                            ";\nflow_vec = " ^ (tmp_gen "initial_flow_vec") ^
                                            ";\nflow_chain = " ^ (tmp_gen "initial_flow_chain") ^
                                            ";\nfidbid_veca = " ^ (tmp_gen "initial_fidbid_veca") ^
                                            ";\nip_veca = " ^ (tmp_gen "initial_ip_veca") ^
                                            ";\nbackends_veca = " ^ (tmp_gen "initial_backends_veca") ^
                                            ";\nbackend_ip_map = " ^ (tmp_gen "initial_backend_ip_map") ^
                                            ";\nactive_backends = " ^ (tmp_gen "initial_active_backends") ^
                                            ";\ncht = " ^ (tmp_gen "initial_cht") ^
                                            ";\n} @*/");
                                       ];};
     "dchain_allocate", {ret_type = Static Sint32;
                         arg_types = stt [Sint32; Ptr (Ptr dchain_struct)];
                         extra_ptr_types = [];
                         lemmas_before = [];
                         lemmas_after = [
                           on_rez_nonzero
                             "if (!dchain_flow_allocated) {\n\
                              assert vectorp<LoadBalancedFlowi>(_, _, ?allocated_vector, _);\n\
                              empty_map_vec_dchain_coherent\
                              <LoadBalancedFlowi>(allocated_vector);\n\
                              } else {\n\
                              assert vectorp<ip_addri>(the_ip_vector, ip_addrp, ?allocated_ip_vector, _);\n\
                              empty_map_vec_dchain_coherent\
                              (allocated_ip_vector);\n\
                              }";
                           (fun _ -> "dchain_flow_allocated = true;");
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
                                           LoadBalancedFlowi>(?" ^
                                          (tmp_gen "cur_map") ^ ", ?" ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^
                                          ");\n\
                                           mvc_coherent_alloc_is_halfowned<LoadBalancedFlowi>(" ^
                                          (tmp_gen "cur_map") ^ ", " ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^ ", *" ^
                                          (List.nth_exn args 1) ^ ");\n} else " ^
                                          "{\n\
                                           assert map_vec_chain_coherent<\
                                           ip_addri>(?" ^
                                          (tmp_gen "cur_map") ^ ", ?" ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^
                                          ");\n\
                                           mvc_coherent_alloc_is_halfowned<ip_addri>(" ^
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
                                      let capture_mvc_args =
                                        "?" ^ (tmp_gen "cur_map") ^ ", ?" ^
                                        (tmp_gen "cur_vec") ^ ", " ^
                                        (tmp_gen "cur_ch")
                                      in
                                      let mvc_args = 
                                        (tmp_gen "cur_map") ^ ", " ^
                                        (tmp_gen "cur_vec") ^ ", " ^
                                        (tmp_gen "cur_ch")
                                      in
                                      "/*@ if (last_map_accessed_lb_flowi) {\n\
                                        assert map_vec_chain_coherent<\
                                       LoadBalancedFlowi>(" ^
                                      capture_mvc_args ^
                                      ");\n\
                                       mvc_coherent_same_len(" ^
                                      mvc_args ^ ");\n} else if (last_map_accessed_ip_addri) {\n" ^
                                        "assert map_vec_chain_coherent<ip_addri>(" ^
                                      capture_mvc_args ^
                                      ");\n\
                                       mvc_coherent_same_len(" ^
                                      mvc_args ^ ");\n} else {\n" ^
                                        "assert map_vec_chain_coherent<uint32_t>(" ^
                                      capture_mvc_args ^
                                      ");\n\
                                       mvc_coherent_same_len(" ^
                                      mvc_args ^ ");\n} @*/";);
                                   (fun {args;tmp_gen;_} ->
                                      "//@ rejuvenate_keeps_high_bounded(" ^
                                      (tmp_gen "cur_ch") ^
                                      ", " ^ (List.nth_exn args 1) ^
                                      ", " ^ (List.nth_exn args 2) ^
                                      ");\n");];
                                 lemmas_after = [
                                   (fun params ->
                                      let rej_last_args = 
                                        (List.nth_exn params.args 1) ^ ", " ^
                                        (List.nth_exn params.args 2)
                                      in
                                      "/*@ if (" ^ params.ret_name ^
                                      " != 0) { \n" ^
                                      "if (last_map_accessed_lb_flowi) {\n\
                                       assert map_vec_chain_coherent<LoadBalancedFlowi>\
                                       (?cur_map,?cur_vec,?cur_ch);\n" ^
                                      "mvc_rejuvenate_preserves_coherent(cur_map,\
                                       cur_vec, cur_ch, " ^
                                      rej_last_args ^
                                      ");\n\
                                       rejuvenate_preserves_index_range(cur_ch," ^
                                      rej_last_args ^ ");\n } else if (last_map_accessed_ip_addri) {\n" ^
                                      "assert map_vec_chain_coherent<ip_addri>\
                                       (?cur_map,?cur_vec,?cur_ch);\n" ^
                                      "mvc_rejuvenate_preserves_coherent(cur_map,\
                                       cur_vec, cur_ch, " ^
                                      rej_last_args ^
                                      ");\n\
                                       rejuvenate_preserves_index_range(cur_ch," ^
                                      rej_last_args ^
                                      ");\n} else {\n" ^
                                      "assert map_vec_chain_coherent<uint32_t>\
                                       (?cur_map,?cur_vec,?cur_ch);\n" ^
                                      "mvc_rejuvenate_preserves_coherent(cur_map,\
                                       cur_vec, cur_ch, " ^
                                      rej_last_args ^
                                      ");\n\
                                       rejuvenate_preserves_index_range(cur_ch," ^
                                      rej_last_args ^
                                      ");\n}\n}@*/");
                                   (fun params ->
                                      (ttype_to_str (List.nth_exn params.arg_types 1)) ^
                                      " the_index_rejuvenated = " ^
                                      (List.nth_exn params.args 1) ^ ";\n");
                                 ];};

     "dchain_is_index_allocated", {ret_type = Static Sint32;
                                   arg_types = stt [Ptr dchain_struct;
                                                    Sint32];
                                   extra_ptr_types = [];
                                   lemmas_before = [];
                                   lemmas_after = [];};
     "dchain_free_index", {ret_type = Static Sint32;
                           arg_types = stt [Ptr dchain_struct;
                                            Sint32];
                           extra_ptr_types = [];
                           lemmas_before = [
                             (fun {tmp_gen;args;_} ->
                                "//@ assert double_chainp(?" ^ (tmp_gen "ch") ^
                                ", " ^ (List.nth_exn args 0) ^ ");\n" ^
                                "//@ assert map_vec_chain_coherent<LoadBalancedFlowi>(?" ^
                                (tmp_gen "map") ^ ", ?" ^
                                (tmp_gen "vec") ^ ", " ^
                                (tmp_gen "ch") ^ ");\n" ^
                                "//@ mvc_coherent_erase(" ^
                                (tmp_gen "map") ^ ", " ^
                                (tmp_gen "vec") ^ ", " ^
                                (tmp_gen "ch") ^ ", last_flow_searched_in_the_map);\n" ^
                                "//@ remove_index_keeps_high_bounded(" ^
                                (tmp_gen "ch") ^ ", " ^
                                (List.nth_exn args 1) ^ ");\n" ^
                                "//@ dchain_remove_keeps_ir(" ^
                                (tmp_gen "ch") ^ ", allocated_index_0);\n"
                             )];
                           lemmas_after = [];};
     "expire_items_single_map", {ret_type = Static Sint32;
                                 arg_types = stt [Ptr dchain_struct;
                                                  Ptr vector_struct;
                                                  Ptr map_struct;
                                                  vigor_time_t];
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
                                       close hide_mapp<LoadBalancedFlowi>(_, _, _, _, _);\n\
                                       }";
                                 ];
                                 lemmas_after = [
                                   (fun _ -> "if (!map_flow_expired) {\n\
                                              map_flow_expired = true;\n\
                                              } else {\n\
                                              //@ open hide_mapp<LoadBalancedFlowi>(_, _, _, _, _);\n\
                                              }");
                                   (fun {tmp_gen;_} ->
                                      "/*@ {\n\
                                       assert mapp<LoadBalancedFlowi>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "fi") ^ ", _));\n\
                                       assert vectorp<LoadBalancedBackendi>(_, _, ?" ^ (tmp_gen "fb") ^ ", _);\n\
                                       assert map_vec_chain_coherent<LoadBalancedFlowi>(" ^
                                      (tmp_gen "fi") ^ ", ?" ^
                                      (tmp_gen "fh") ^ ", ?" ^
                                      (tmp_gen "ch") ^
                                      ");\n\
                                       assert mapp<LoadBalancedFlowi>(_, _, _, _, ?" ^ (tmp_gen "fi_full") ^ ");\n\
                                      mvc_coherent_same_len<LoadBalancedFlowi>(" ^
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
                            map_keys_equality<LoadBalancedFlowi>(LoadBalancedFlow_eq)\
                            (LoadBalancedFlowp)(a, b) \
                            {\
                            call();\
                            }\n\
                            produce_function_pointer_chunk \
                            map_key_hash<LoadBalancedFlowi>(LoadBalancedFlow_hash)\
                            (LoadBalancedFlowp, _LoadBalancedFlow_hash)(a) \
                            {\
                            call();\
                            }\n\
                             } else {\nproduce_function_pointer_chunk \
                            map_keys_equality<ip_addri>(ip_addr_eq)\
                            (ip_addrp)(a, b) \
                            {\
                            call();\
                            }\n\
                            produce_function_pointer_chunk \
                            map_key_hash<ip_addri>(ip_addr_hash)\
                            (ip_addrp, _ip_addr_hash)(a) \
                            {\
                            call();\
                            }\n\
                            } @*/ \n");];
                      lemmas_after = [
                        (fun {tmp_gen;ret_name;_} -> (* see remark above *)
                            "/*@ if (!map_flow_allocated) {\n assert [?" ^ (tmp_gen "imkedy") ^
                           "]is_map_keys_equality(LoadBalancedFlow_eq,\
                            LoadBalancedFlowp);\n\
                            close [" ^ (tmp_gen "imkedy") ^
                           "]hide_is_map_keys_equality(LoadBalancedFlow_eq, \
                            LoadBalancedFlowp);\n\
                            assert [?" ^ (tmp_gen "imkhdy") ^
                           "]is_map_key_hash(LoadBalancedFlow_hash,\
                            LoadBalancedFlowp, _LoadBalancedFlow_hash);\n\
                            close [" ^ (tmp_gen "imkhdy") ^
                           "]hide_is_map_key_hash(LoadBalancedFlow_hash, \
                            LoadBalancedFlowp, _LoadBalancedFlow_hash);\n\
                            } else {\n assert [?" ^ (tmp_gen "imkedy") ^
                           "]is_map_keys_equality(ip_addr_eq,\
                            ip_addrp);\n\
                            close [" ^ (tmp_gen "imkedy") ^
                           "]hide_is_map_keys_equality(ip_addr_eq, \
                            ip_addrp);\n\
                            assert [?" ^ (tmp_gen "imkhdy") ^
                           "]is_map_key_hash(ip_addr_hash,\
                            ip_addrp, _ip_addr_hash);\n\
                            close [" ^ (tmp_gen "imkhdy") ^
                           "]hide_is_map_key_hash(ip_addr_hash, \
                            ip_addrp, _ip_addr_hash);\n\
                            if (" ^ ret_name ^
                            " == 1) {\n\
                            assert mapp<ip_addri>(_, _, _, _, mapc(?" ^ (tmp_gen "cap") ^
                            ", ?" ^ (tmp_gen "map") ^
                            ", ?" ^ (tmp_gen "addr_map") ^
                            "));\n\
                             assert vectorp<ip_addri>(the_ip_vector, _, ?" ^
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
                                       "ip_addr", Ptr ip_addr_struct];
                              Static (Ptr Sint32)];
                 extra_ptr_types = [];
                 lemmas_before = [
                   (fun ({arg_types;arg_exps;tmp_gen;_} as params) ->
                      match List.nth_exn arg_types 1 with
                      | Ptr (Str ("LoadBalancedFlow", _)) ->
                        "//@ assert LoadBalancedFlowp(" ^ (render_tterm (List.nth_exn arg_exps 1)) ^
                        ", ?" ^ (tmp_gen "dk") ^ ");\n" ^
                        "//@ last_flow_searched_in_the_map = " ^
                        (tmp_gen "dk") ^ ";\n" ^
                         capture_a_map "LoadBalancedFlowi" "dm" params ^
                         "//@ assert map_vec_chain_coherent<LoadBalancedFlowi>(" ^
                         (tmp_gen "dm") ^ ", ?" ^
                         (tmp_gen "dv") ^ ", ?" ^
                         (tmp_gen "dh") ^ ");\n" ^
                        "/*@ { close hide_mapp<ip_addri>(_, _, _, _, _); } @*/\n"
                      | Ptr (Str ("ip_addr", _)) ->
                         capture_a_map "ip_addri" "dm" params ^
                         "//@ assert map_vec_chain_coherent<ip_addri>(" ^
                         (tmp_gen "dm") ^ ", ?" ^
                         (tmp_gen "dv") ^ ", ?" ^
                         (tmp_gen "dh") ^ ");\n" ^
                        "/*@ { close hide_mapp<LoadBalancedFlowi>(_, _, _, _, _); } @*/\n"
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
                         mvc_coherent_map_get(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ", " ^
                        (tmp_gen "dk") ^ ");\n\
                         } @*/\n\
                        last_map_accessed_lb_flowi = true;\n" ^
                        "last_map_accessed_ip_addri = false;\n" ^
                        "/*@ { open hide_mapp<ip_addri>(_, _, _, _, _); } @*/\n"
                      | Ptr (Str ("ip_addr", _)) ->
                        "/*@ if (" ^ ret_name ^
                        " != 0) {\n\
                         assert ip_addrp(" ^ (List.nth_exn args 1) ^ ", ?" ^
                        (tmp_gen "ip") ^ ");\n" ^
                        "mvc_coherent_map_get_bounded(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ", " ^
                        (tmp_gen "ip") ^
                        ");\n\
                         mvc_coherent_map_get_vec_half(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ", " ^
                        (tmp_gen "ip") ^
                        ");\n\
                         } @*/\n\
                        last_map_accessed_lb_flowi = false; \n" ^
                        "last_map_accessed_ip_addri = true;\n" ^
                        "/*@ { open hide_mapp<LoadBalancedFlowi>(_, _, _, _, _); } @*/\n"
                      | _ -> failwith "unexpected key type for map_get.");
                   (fun params -> "if (" ^ params.ret_name ^ " != 0) { backend_known = true; backend_index = *" ^ (List.nth_exn params.args 2) ^ "; }\n" );];};
     "map_put", {ret_type = Static Void;
                 arg_types = [Static (Ptr map_struct);
                              Dynamic ["LoadBalancedFlow", (Ptr lb_flow_struct);
                                       "ip_addr", Ptr ip_addr_struct;
                                       "uint32_t", Ptr Uint32];
                              Static Sint32];
                 extra_ptr_types = [];
                 lemmas_before = [
                   (fun {args;tmp_gen;arg_types;_} ->
                      match List.nth_exn arg_types 1 with
                      | Ptr (Str ("LoadBalancedFlow", _)) ->
                        "\n//@ assert mapp<LoadBalancedFlowi>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "dm") ^
                        ", _));\n" ^
                        "\n/*@ {\n\
                         assert map_vec_chain_coherent<LoadBalancedFlowi>(" ^
                        (tmp_gen "dm") ^ ", ?" ^
                        (tmp_gen "dv") ^ ", ?" ^
                        (tmp_gen "dh") ^
                        ");\n\
                         mvc_coherent_dchain_non_out_of_space_map_nonfull<LoadBalancedFlowi>(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ");\n" ^
                         "mvc_coherent_bounds<LoadBalancedFlowi>(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ");\n} @*/\n" ^
                        let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
                        "/*@ { \n\
                         assert mapp<LoadBalancedFlowi>(_, _, _, _, mapc(_, _, ?dm_addrs)); \n\
                         assert vectorp<LoadBalancedFlowi>(_, _, _, ?dv_addrs); \n\
                         assert map_vec_chain_coherent<LoadBalancedFlowi>(?the_dm, ?the_dv, ?the_dh);\n\
                         LoadBalancedFlowi vvv = LoadBalancedFlowc(" ^ arg1 ^
                        "->src_ip, " ^ arg1 ^
                        "->dst_ip, " ^ arg1 ^
                        "->src_port, " ^ arg1 ^
                        "->dst_port, " ^ arg1 ^
                        "->protocol); \n\
                         mvc_coherent_key_abscent(the_dm, the_dv, the_dh, vvv);\n\
                         kkeeper_add_one(dv_addrs, the_dv, dm_addrs, vvv, " ^ (List.nth_exn args 2) ^
                        "); \n\
                         } @*/\n" ^
                        "/*@ { close hide_mapp<ip_addri>(_, _, _, _, _); } @*/\n"
                      | Ptr (Str ("ip_addr", _)) ->
                        "\n//@ assert mapp<ip_addri>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "dm") ^
                        ", _));\n" ^
                        "\n/*@ {\n\
                         assert map_vec_chain_coherent<ip_addri>(" ^
                        (tmp_gen "dm") ^ ", ?" ^
                        (tmp_gen "dv") ^ ", ?" ^
                        (tmp_gen "dh") ^
                        ");\n\
                         mvc_coherent_dchain_non_out_of_space_map_nonfull(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ");\n} @*/\n" ^
                        let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
                        "/*@ { \n\
                         assert mapp<ip_addri>(_, _, _, _, mapc(_, _, ?dm_addrs)); \n\
                         assert vectorp<ip_addri>(_, _, _, ?dv_addrs); \n\
                         assert map_vec_chain_coherent<ip_addri>(?the_dm, ?the_dv, ?the_dh);\n\
                         close ip_addrp(" ^ arg1 ^ ", ?vvv)" ^
                        "; \n\
                         mvc_coherent_key_abscent(the_dm, the_dv, the_dh, vvv);\n\
                         kkeeper_add_one(dv_addrs, the_dv, dm_addrs, vvv, " ^ (List.nth_exn args 2) ^
                        "); \n\
                         } @*/\n" ^
                        "/*@ { close hide_mapp<LoadBalancedFlowi>(_, _, _, _, _); } @*/\n"
                      | _ -> failwith "unexpected key type for map_put.");];
                 lemmas_after = [
                   (fun {args;tmp_gen;arg_types;_} ->
                      match List.nth_exn arg_types 1 with
                      | Ptr (Str ("LoadBalancedFlow", _)) ->
                        let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
                        "\n/*@ {\n\
                         assert map_vec_chain_coherent<LoadBalancedFlowi>(" ^ (tmp_gen "dm") ^
                        ", ?" ^ (tmp_gen "dv") ^
                        ", ?" ^ (tmp_gen "dh") ^
                        ");\n\
                         LoadBalancedFlowi " ^ (tmp_gen "ea") ^ " = LoadBalancedFlowc(" ^ arg1 ^
                        "->src_ip, " ^ arg1 ^
                        "->dst_ip, " ^ arg1 ^
                        "->src_port, " ^ arg1 ^
                        "->dst_port, " ^ arg1 ^
                        "->protocol);\n\
                         mvc_coherent_put<LoadBalancedFlowi>(" ^ (tmp_gen "dm") ^
                        ", " ^ (tmp_gen "dv") ^
                        ", " ^ (tmp_gen "dh") ^
                        ", " ^ (List.nth_exn args 2) ^
                        ", time_for_allocated_index, " ^ (tmp_gen "ea") ^
                        ");\n\
                         } @*/\n" ^
                        "/*@ { open hide_mapp<ip_addri>(_, _, _, _, _); } @*/\n"
                      | Ptr (Str ("ip_addr", _)) ->
                        let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
                        "\n/*@ {\n\
                         assert map_vec_chain_coherent<ip_addri>(" ^ (tmp_gen "dm") ^
                        ", ?" ^ (tmp_gen "dv") ^
                        ", ?" ^ (tmp_gen "dh") ^
                        ");\n\
                         ip_addri " ^ (tmp_gen "ea") ^ " = ip_addrc(" ^ arg1 ^
                        "->addr);\n\
                         mvc_coherent_put<ip_addri>(" ^ (tmp_gen "dm") ^
                        ", " ^ (tmp_gen "dv") ^
                        ", " ^ (tmp_gen "dh") ^
                        ", " ^ (List.nth_exn args 2) ^
                        ", time_for_allocated_index, " ^ (tmp_gen "ea") ^
                        ");\n\
                         } @*/\n" ^
                        "/*@ { open hide_mapp<LoadBalancedFlowi>(_, _, _, _, _); } @*/\n"
                      | _ -> failwith "unexpected key type for map_put.");
                   (fun params -> "backend_known = true;\nbackend_index = " ^ (List.nth_exn params.args 2) ^ ";\n");];};
     "map_erase", {ret_type = Static Void;
                   arg_types = [Static (Ptr map_struct);
                                Dynamic ["LoadBalancedFlow", (Ptr lb_flow_struct);
                                         "ip_addr", Ptr ip_addr_struct];
                                Dynamic ["LoadBalancedFlow", Ptr (Ptr lb_flow_struct);
                                         "ip_addr", Ptr (Ptr ip_addr_struct)];];
                   extra_ptr_types = [];
                   lemmas_before = [
                     (fun {args;arg_types;_} ->
                        match List.nth_exn arg_types 1 with
                        | Ptr (Str ("LoadBalancedFlow", _)) ->
                          "/*@ { close hide_mapp<ip_addri>(_, _, _, _, _); } @*/\n" ^
                          let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
                        "/*@ { \n\
                         assert mapp<LoadBalancedFlowi>(_, _, _, _, mapc(_, ?dm, ?dm_addrs)); \n\
                         assert vectorp<LoadBalancedFlowi>(_, _, _, ?dv_addrs); \n\
                         assert map_vec_chain_coherent<LoadBalancedFlowi>(?the_dm, ?the_dv, ?the_dh);\n\
                          assert LoadBalancedFlowp(" ^ arg1 ^ ", ?vvv);\n\
                         kkeeper_erase_one(dv_addrs, the_dv, dm_addrs, map_get_fp(dm, vvv));\n\
                         } @*/\n"
                        | Ptr (Str ("ip_addr", _)) ->
                          "/*@ { close hide_mapp<LoadBalancedFlowi>(_, _, _, _, _); } @*/\n"
                        | _ -> failwith "unexpected key type for map_erase")
                   ];
                   lemmas_after = [
                     (fun {arg_types;_} ->
                        match List.nth_exn arg_types 1 with
                        | Ptr (Str ("LoadBalancedFlow", _)) ->
                          "/*@ { open hide_mapp<ip_addri>(_, _, _, _, _); } @*/\n"
                        | Ptr (Str ("ip_addr", _)) ->
                          "/*@ { open hide_mapp<LoadBalancedFlowi>(_, _, _, _, _); } @*/\n"
                        | _ -> failwith "unexpected key type for map_erase")];};
     "map_size", {ret_type = Static Sint32;
                  arg_types = [Static (Ptr map_struct);];
                  extra_ptr_types = [];
                  lemmas_before = [];
                  lemmas_after = [];};
     "cht_find_preferred_available_backend", {
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
                     lemmas_after = [(fun {args;_} ->
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
                             lemmas_after = [(fun {arg_exps;tmp_gen;_} ->
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
                                produce_function_pointer_chunk vector_init_elem<LoadBalancedFlowi>(LoadBalancedFlow_allocate)\
                                (LoadBalancedFlowp, sizeof(struct LoadBalancedFlow))(a) \
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
                                produce_function_pointer_chunk vector_init_elem<ip_addri>(ip_addr_allocate)\
                                (ip_addrp, sizeof(struct ip_addr))(a) \
                                {\
                                call();\
                                }\n\
                              } else if(!vector_backends_allocated) {\n\
                                produce_function_pointer_chunk vector_init_elem<LoadBalancedBackendi>(LoadBalancedBackend_allocate)\
                                (LoadBalancedBackendp, sizeof(struct LoadBalancedBackend))(a) \
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
                               assert mapp<LoadBalancedFlowi>(_, _, _, _, mapc(?" ^ (tmp_gen "cap") ^
                              ", ?" ^ (tmp_gen "map") ^
                              ", ?" ^ (tmp_gen "addr_map") ^
                              "));\n\
                               assert vectorp<LoadBalancedFlowi>(_, _, ?" ^ (tmp_gen "dks") ^
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
     "cht_fill_cht",        {ret_type = Static Void;
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
                                                  "ip_addr", Ptr (Ptr ip_addr_struct);
                                                  "uint32_t", Ptr (Ptr Uint32)];];
                            extra_ptr_types = ["borrowed_cell",
                                               Dynamic ["LoadBalancedFlow", Ptr lb_flow_struct;
                                                        "LoadBalancedBackend", Ptr lb_backend_struct;
                                                        "ip_addr", Ptr ip_addr_struct;
                                                        "uint32_t", Ptr Uint32];];
                            lemmas_before = [
                              (fun params ->
                                 match List.nth_exn params.arg_types 2 with
                                 | Ptr (Ptr (Str ("LoadBalancedFlow", _))) ->
                                   "/*@ { close hide_vector<LoadBalancedBackendi>(_, _, _, _); } @*/\n" ^
                                   "//@ close hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ close hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ close hide_vector<ip_addri>(_, _, _, _);\n" ^
                                   "//@ assert vectorp<LoadBalancedFlowi>(" ^ (List.nth_exn params.args 0) ^
                                   ", LoadBalancedFlowp, ?" ^ (params.tmp_gen "vec") ^ ", ?" ^ (params.tmp_gen "veca") ^
                                   ");\n//@ vector_addrs_same_len_nodups(" ^ (List.nth_exn params.args 0) ^ ");\n"
                                 | Ptr (Ptr (Str ("LoadBalancedBackend", _))) ->
                                   "/*@ { close hide_vector<LoadBalancedFlowi>(_, _, _, _); } @*/\n" ^
                                   "/*@ { assert vectorp<LoadBalancedBackendi>(_, _, ?" ^ (params.tmp_gen "vec") ^ ", _);\n\
                                          forall_mem(nth(" ^ (List.nth_exn params.args 1) ^ ", " ^ (params.tmp_gen "vec") ^ "), " ^ (params.tmp_gen "vec") ^ ", is_one);\n } @*/\n" ^
                                   "//@ close hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ close hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ close hide_vector<ip_addri>(_, _, _, _);\n"
                                 | Ptr (Ptr Uint32) ->
                                   "//@ close hide_vector<LoadBalancedBackendi>(_, _, _, _);\n" ^
                                   "/*@ { close hide_vector<LoadBalancedFlowi>(_, _, _, _); } @*/\n" ^
                                   "/*@ { assert vectorp<uint32_t>(" ^ (List.nth_exn params.args 0) ^ ", _, ?" ^
                                   (params.tmp_gen "vec") ^
                                   ", _);\n\
                                    if (forall(" ^ (params.tmp_gen "vec") ^
                                   ", is_one)) {\n\
                                    forall_mem(nth(" ^ (List.nth_exn params.args 1) ^ ", " ^
                                   (params.tmp_gen "vec") ^ "), " ^ (params.tmp_gen "vec") ^ ", is_one);\n }\n}\n @*/\n" ^
                                   "//@ close hide_vector<ip_addri>(_, _, _, _);\n"
                                 | Ptr (Ptr (Str ("ip_addr", _))) ->
                                   "//@ close hide_vector<LoadBalancedBackendi>(_, _, _, _);\n" ^
                                   "//@ close hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ close hide_vector<uint32_t>(_, _, _, _);\n" ^
                                   "/*@ { close hide_vector<LoadBalancedFlowi>(_, _, _, _); } @*/\n" ^
                                   "/*@ { assert vectorp<ip_addri>(" ^ (List.nth_exn params.args 0) ^ ", _, ?" ^
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
                                   "/*@ { open hide_vector<LoadBalancedBackendi>(_, _, _, _); } @*/\n" ^
                                   "//@ open hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ open hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ open hide_vector<ip_addri>(_, _, _, _);\n" ^
                                   "/*@ {\n\
                                    assert mapp<LoadBalancedFlowi>(_, _, _, _, mapc(_,?" ^ (params.tmp_gen "fm") ^
                                   ", ?" ^ (params.tmp_gen "fma") ^
                                   "));\n\
                                    forall2_nth(" ^ (params.tmp_gen "vec") ^ ", " ^ (params.tmp_gen "veca") ^
                                   ", (kkeeper)(" ^ (params.tmp_gen "fma") ^ "), " ^ (List.nth_exn params.args 1) ^
                                   ");\n} @*/ "
                                 | Ptr (Ptr (Str ("LoadBalancedBackend", _))) ->
                                   let (binding,expr) =
                                     self_dereference (List.nth_exn params.arg_exps 2) params.tmp_gen
                                   in
                                   binding ^ "\n" ^
                                   "//@ open [_]ether_addrp(" ^ (render_tterm expr) ^ "->mac, _);\n" ^
                                   "/*@ { open hide_vector<LoadBalancedFlowi>(_, _, _, _); } @*/\n" ^
                                   "//@ open hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ open hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ open hide_vector<ip_addri>(_, _, _, _);\n"
                                 | Ptr (Ptr Uint32) ->
                                   "//@ open hide_vector<LoadBalancedBackendi>(_, _, _, _);\n" ^
                                   "/*@ { open hide_vector<LoadBalancedFlowi>(_, _, _, _); } @*/\n" ^
                                   "//@ open hide_vector<ip_addri>(_, _, _, _);\n"
                                 | Ptr (Ptr (Str ("ip_addr", _))) ->
                                   "//@ open hide_vector<LoadBalancedBackendi>(_, _, _, _);\n" ^
                                   "//@ open hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ open hide_vector<uint32_t>(_, _, _, _);\n" ^
                                   "/*@ { open hide_vector<LoadBalancedFlowi>(_, _, _, _); } @*/\n"
                                 | _ ->
                                   failwith "Unsupported type for vector!")
                            ];};
     "vector_return",      {ret_type = Static Void;
                            arg_types = [Static (Ptr vector_struct);
                                         Static Sint32;
                                         Dynamic ["LoadBalancedFlow", Ptr lb_flow_struct;
                                                  "LoadBalancedBackend", Ptr lb_backend_struct;
                                                  "ip_addr", Ptr ip_addr_struct;
                                                  "uint32_t", Ptr Uint32];];
                            extra_ptr_types = [];
                            lemmas_before = [
                              (fun params ->
                                 match List.nth_exn params.arg_types 2 with
                                 | Ptr (Str ("LoadBalancedFlow", _)) ->
                                   "/*@ close hide_vector<LoadBalancedBackendi>(_, _, _, _); @*/\n" ^
                                   "//@ close hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ close hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ close hide_vector<ip_addri>(_, _, _, _);\n"
                                 | Ptr (Str ("LoadBalancedBackend", _)) ->
                                   "/*@ close hide_vector<LoadBalancedFlowi>(_, _, _, _); @*/\n" ^
                                   "//@ close hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ close hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ close hide_vector<ip_addri>(_, _, _, _);\n"
                                 | Ptr Uint32 ->
                                   "/*@ close hide_vector<LoadBalancedBackendi>(_, _, _, _); @*/\n" ^
                                   "/*@ close hide_vector<LoadBalancedFlowi>(_, _, _, _); @*/\n" ^
                                   "//@ close hide_vector<ip_addri>(_, _, _, _);\n"
                                 | Ptr (Str ("ip_addr", _)) -> 
                                   "/*@ close hide_vector<LoadBalancedBackendi>(_, _, _, _); @*/\n" ^
                                   "/*@ close hide_vector<LoadBalancedFlowi>(_, _, _, _); @*/\n" ^
                                   "//@ close hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ close hide_vector<uint32_t>(_, _, _, _);\n"
                                 | _ ->
                                   failwith "Unsupported type for vector!");
                              (fun params ->
                                 match List.nth_exn params.arg_types 2 with
                                 | Ptr (Str ("LoadBalancedFlow", _)) -> (* see remark in return_full *)
                                   "/*@ { assert vectorp<LoadBalancedFlowi>(_, _, ?" ^ (params.tmp_gen "vec") ^ ", _); \n\
                                          update_id(" ^ (List.nth_exn params.args 1) ^ ", " ^ (params.tmp_gen "vec") ^ "); } @*/"
                                 | Ptr (Str ("LoadBalancedBackend", _)) ->
                                   "/*@ { assert vectorp<LoadBalancedBackendi>(_, _, ?" ^ (params.tmp_gen "vec") ^
                                   ", _); \n\
                                    assert *&" ^
                                   (Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn params.args 2)) ^
                                   " |-> ? " ^ (params.tmp_gen "bknd") ^
                                   ";\n\
                                    assert LoadBalancedBackendp(" ^
                                   (params.tmp_gen "bknd") ^
                                   ", ?" ^ (params.tmp_gen "bknd_logical") ^
                                   ");\n\
                                    update_id(" ^ (List.nth_exn params.args 1) ^ ", " ^ (params.tmp_gen "vec") ^ "); } @*/"
                                 | Ptr Uint32 ->
                                   let arg2 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn params.args 2) in
                                   " uint32_t " ^ (params.tmp_gen "put_value") ^ " = *" ^ arg2 ^
                                   ";\n" ^
                                   "/*@ { assert vectorp<uint32_t>(_, _, ?" ^ (params.tmp_gen "vec") ^
                                   ", _); \n\
                                    if (forall(" ^ (params.tmp_gen "vec") ^
                                   ", is_one)) {\n\
                                    update_id(" ^ (List.nth_exn params.args 1) ^ ", " ^ (params.tmp_gen "vec") ^ "); }\n}@*/"
                                 | Ptr (Str ("ip_addr", _)) ->
                                   let arg2 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn params.args 2) in
                                   "//@ ip_addri " ^ (params.tmp_gen "put_value") ^ " = ip_addrc(" ^ arg2 ^ "->addr" ^
                                   ");\n" ^
                                   "/*@ { assert vectorp<ip_addri>(_, _, ?" ^ (params.tmp_gen "vec") ^
                                   ", _); \n\
                                    if (forall(" ^ (params.tmp_gen "vec") ^
                                   ", is_one)) {\n\
                                    update_id(" ^ (List.nth_exn params.args 1) ^ ", " ^ (params.tmp_gen "vec") ^ "); }\n}@*/"
                                 | _ ->
                                   failwith "Unsupported type for vector!");
                            ];
                            lemmas_after = [
                              (fun params ->
                                 match List.nth_exn params.arg_types 2 with
                                 | Ptr (Str ("LoadBalancedFlow", _)) ->
                                   "/*@ open hide_vector<LoadBalancedBackendi>(_, _, _, _); @*/\n" ^
                                   "//@ open hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ open hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ open hide_vector<ip_addri>(_, _, _, _);\n"
                                 | Ptr (Str ("LoadBalancedBackend", _)) ->
                                   "/*@ open hide_vector<LoadBalancedFlowi>(_, _, _, _); @*/\n" ^
                                   "//@ open hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ open hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ open hide_vector<ip_addri>(_, _, _, _);\n"
                                 | Ptr Uint32 ->
                                   "/*@ open hide_vector<LoadBalancedBackendi>(_, _, _, _); @*/\n" ^
                                   "/*@ open hide_vector<LoadBalancedFlowi>(_, _, _, _); @*/\n" ^
                                   "//@ open hide_vector<ip_addri>(_, _, _, _);\n"
                                 | Ptr (Str ("ip_addr", _)) ->
                                   "/*@ open hide_vector<LoadBalancedBackendi>(_, _, _, _); @*/\n" ^
                                   "/*@ open hide_vector<LoadBalancedFlowi>(_, _, _, _); @*/\n" ^
                                   "//@ open hide_vector<uint32_t>(_, _, _, _);\n\
                                    //@ open hide_vector<uint32_t>(_, _, _, _);\n"
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
#include \"vigbalancer/lb_loop.h\"\n\
#include \"vigbalancer/lb_balancer.h\"\n" ^
                 (In_channel.read_all "preamble.tmpl") ^
                 (In_channel.read_all "preamble_hide.tmpl") ^
                 "void to_verify()\n\
                  /*@ requires true; @*/ \n\
                  /*@ ensures true; @*/\n{\n\
                  //@ modulo_hack();\n\
                  uint16_t received_on_port;\n\
                  int the_index_allocated = -1;\n\
                  int64_t time_for_allocated_index = 0;\n\
                  bool a_packet_received = false;\n\
                  //@ bool packet_is_complete = false;\n\
                  //@ option<void*> last_composed_packet = none;\n\
                  //@ list<uint8_t> last_sent_packet = nil;\n\
                  uint32_t pkt_sent_type;\n\
                  bool backend_known = false;\n\
                  struct Vector* the_ip_vector;\n\
                  int32_t backend_index = -1;\n"
                 ^ "//@ struct Vector* fidbid_veca_ptr;\n\
                    //@ struct Vector* cht_ptr;\n\
                    //@ struct Vector* backends_veca_ptr;\n"
                 ^ "//@ list<pair<LoadBalancedFlowi, uint32_t> > flow_map;\n"
                 ^ "//@ list<pair<LoadBalancedFlowi, real> > flow_vec;\n"
                 ^ "//@ dchain flow_chain;\n"
                 ^ "//@ list<pair<uint32_t, real> > fidbid_veca;\n"
                 ^ "//@ list<pair<ip_addri, real> > ip_veca;\n"
                 ^ "//@ list<pair<LoadBalancedBackendi, real> > backends_veca;\n"
                 ^ "//@ list<pair<ip_addri, uint32_t> > backend_ip_map;\n"
                 ^ "//@ dchain active_backends;\n"
                 ^ "//@ list<pair<uint32_t, real> > cht;\n"
                 ^ "//@ mapi<LoadBalancedFlowi> expired_indices;\n" (*FIXME: these should not be necessary*)
                 ^ "//@ list<pair<LoadBalancedFlowi, real> > expired_heap;\n"
                 ^ "//@ list<pair<LoadBalancedBackendi, real> > expired_backends;\n"
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
                    bool last_map_accessed_ip_addri = false;\n\
                    //@ LoadBalancedFlowi last_flow_searched_in_the_map;\n\
                    //@ list<phdr> recv_headers = nil; \n\
                    //@ list<phdr> sent_headers = nil; \n\
                    //@ list<int> sent_on_ports = nil; \n\
                    //@ assume(sizeof(struct ip_addr) == 4);\n\
                    //@ assume(sizeof(struct ether_hdr) == 14);\n\
                    //@ assume(sizeof(struct tcpudp_hdr) == 4);\n\
                    //@ assume(sizeof(struct ipv4_hdr) == 20);//TODO: handle all this sizeof's explicitly\n\
                 "
  let fun_types = fun_types
  let boundary_fun = "lb_loop_invariant_produce"
  let finishing_fun = "lb_loop_invariant_consume"
  let eventproc_iteration_begin = "lb_loop_invariant_produce"
  let eventproc_iteration_end = "lb_loop_invariant_consume"
  let user_check_for_complete_iteration = In_channel.read_all "balancer_forwarding_property.tmpl"
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

