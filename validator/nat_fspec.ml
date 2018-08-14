open Core
open Str
open Fspec_api
open Ir

type map_key = Int | Ext

let last_index_gotten = ref ""
let last_index_key = ref Int
let last_indexing_succ_ret_var = ref ""
let last_device_id = ref ""

let last_time_for_index_alloc = ref ""


let gen_get_fp map_name =
  match !last_index_key with
  | Int-> "dmap_get_k1_fp(" ^ map_name ^ ", " ^ !last_index_gotten ^ ")"
  | Ext -> "dmap_get_k2_fp(" ^ map_name ^ ", " ^ !last_index_gotten ^ ")"

let capture_map map_name ptr_num {args;tmp_gen;_} =
  "//@ assert dmappingp<flow_id,flow_id,flow>(?" ^ (tmp_gen map_name) ^
  ",_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args ptr_num) ^ ");\n"

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

let dmap_struct = Ir.Str ( "DoubleMap", [] )
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
     "dmap_allocate", {ret_type = Static Sint32;
                       arg_types = stt
                         [Ptr (Ctm "map_keys_equality"); Ptr (Ctm "map_key_hash");
                          Ptr (Ctm "map_keys_equality"); Ptr (Ctm "map_key_hash");
                          Sint32; Ptr (Ctm "uq_value_copy");
                          Ptr (Ctm "uq_value_destr");
                          Ptr (Ctm "dmap_extract_keys"); Ptr (Ctm "dmap_pack_keys");
                          Uint32; Uint32;
                          Ptr (Ptr dmap_struct)];
                       extra_ptr_types = [];
                       lemmas_before = [
                         tx_bl "produce_function_pointer_chunk \
                                map_keys_equality<flow_id>(flow_id_eq)(flow_idp)(a, b) \
                                {\
                                call();\
                                }";
                         tx_bl "produce_function_pointer_chunk \
                                map_key_hash<flow_id>(flow_id_hash)\
                                (flow_idp, _flow_id_hash)(a)\
                                {\
                                call();\
                                }";
                         tx_bl "produce_function_pointer_chunk \
                                map_keys_equality<flow_id>(flow_id_eq)(flow_idp)(a, b)\
                                {\
                                call();\
                                }";
                         tx_bl "produce_function_pointer_chunk \
                                map_key_hash<flow_id>(flow_id_hash)\
                                (flow_idp, _flow_id_hash)(a)\
                                {\
                                call();\
                                }";
                         tx_bl "produce_function_pointer_chunk \
                                dmap_extract_keys<flow_id,flow_id,flow>\
                                (flow_extract_keys)\
                                (flow_idp, flow_idp, flowp, flowp_bare,\
                                 flow_ids_offsets_fp,\
                                 flow_get_internal_id,\
                                 flow_get_external_id)(a, b, c)\
                                {\
                                call();\
                                }";
                         tx_bl "produce_function_pointer_chunk \
                                dmap_pack_keys<flow_id,flow_id,flow>\
                                (flow_pack_keys)\
                                (flow_idp, flow_idp, flowp, flowp_bare,\
                                 flow_ids_offsets_fp,\
                                 flow_get_internal_id,\
                                 flow_get_external_id)(a, b, c)\
                                {\
                                call();\
                                }";
                         tx_bl "produce_function_pointer_chunk \
                                uq_value_destr<flow>\
                                (flow_destroy)\
                                (flowp, sizeof(struct Flow))(a)\
                                {\
                                call();\
                                }";
                         (fun {args;_} ->
                            "/*@\
                             assume(sizeof(struct Flow) == " ^
                            (List.nth_exn args 4) ^ ");\n@*/ " ^
                             "/*@ produce_function_pointer_chunk \
                             uq_value_copy<flow>(flow_copy)\
                             (flowp, " ^ (List.nth_exn args 4) ^ ")(a,b)\
                             {\
                             call();\
                             }@*/");
                         tx_bl "close dmap_key_val_types\
                                (flid(0,0,0,0,0), flid(0,0,0,0,0),\
                                      flw(flid(0,0,0,0,0),flid(0,0,0,0,0),0));";
                         tx_bl "close dmap_record_property1(nat_int_fp);";
                         (fun _ -> "int start_port;\n");
                         tx_bl "close dmap_record_property2\
                                ((nat_ext_fp)(start_port));"];
                       lemmas_after = [
                         tx_l "empty_dmap_cap\
                               <flow_id,flow_id,flow>(65536);";];};
     "dchain_allocate", {ret_type = Static Sint32;
                         arg_types = stt [Sint32; Ptr (Ptr dchain_struct)];
                         extra_ptr_types = [];
                         lemmas_before = [];
                         lemmas_after = [
                           on_rez_nonzero
                               "empty_dmap_dchain_coherent\
                                <flow_id,flow_id,flow>(65536);";
                           tx_l "index_range_of_empty(65536, 0);";];};
     "loop_invariant_consume", {ret_type = Static Void;
                                arg_types = stt [Ptr (Ptr dmap_struct);
                                             Ptr (Ptr dchain_struct);
                                             Uint32;
                                             Sint64;
                                             Sint32;
                                             Sint32];
                                extra_ptr_types = [];
                                lemmas_before = [
                                  (fun {args;_} ->
                                     "//@ assume(start_port == " ^
                                     List.nth_exn args 5 ^");");
                                  (fun {args;_} ->
                                     "/*@ close evproc_loop_invariant(*" ^
                                     List.nth_exn args 0 ^ ", *" ^
                                     List.nth_exn args 1 ^ ", " ^
                                     List.nth_exn args 2 ^ ", " ^
                                     List.nth_exn args 3 ^ ", " ^
                                     List.nth_exn args 4 ^ ", " ^
                                     List.nth_exn args 5 ^ "); @*/");
                                ];
                                lemmas_after = [];};
     "loop_invariant_produce", {ret_type = Static Void;
                                arg_types = stt [Ptr (Ptr dmap_struct);
                                             Ptr (Ptr dchain_struct);
                                             Ptr Uint32;
                                             Ptr Sint64;
                                             Sint32;
                                             Sint32];
                                extra_ptr_types = [];
                                lemmas_before = [
                                  (fun _ ->
                                     "int start_port;\n");];
                                lemmas_after = [
                                  (fun params ->
                                     "/*@ open evproc_loop_invariant(?mp, \
                                      ?chp, *" ^
                                     List.nth_exn params.args 2 ^ ", *" ^
                                     List.nth_exn params.args 3 ^ ", " ^
                                     List.nth_exn params.args 4 ^ ", " ^
                                     List.nth_exn params.args 5 ^ ");@*/");
                                  (fun params ->
                                     "//@ assume(" ^
                                     List.nth_exn params.args 5 ^ " == start_port);");
                                  tx_l "assert dmap_dchain_coherent(?map,?chain);";
                                  tx_l "coherent_same_cap(map, chain);";
                                  tx_l "dmap<flow_id,flow_id,flow> initial_double_map = map;";
                                  tx_l "dchain initial_double_chain = chain;"
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
                    ".external_id, flid(new_index_2_0, dp, external_ip, dip, user_buf_23));\n" ^
                    " close flowp(" ^ (List.nth_exn args 1) ^
                    ", flw(flid(isp, dp, isip, dip, user_buf_23),
                           flid(new_index_2_0, dp, external_ip, dip, user_buf_23), " ^
                           !last_device_id ^ "));\n" ^
                       "assert dmap_dchain_coherent(" ^
                         (tmp_gen "cur_map") ^
                       ", ?cur_ch);\n\
                        flow_id ek = flid(new_index_2_0, dp,\
                        external_ip, dip, user_buf_23);\n\
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
                        flid(new_index_2_0, dp, external_ip, dip,\
                        user_buf_23)," ^ !last_device_id ^ ")," ^
                       (tmp_gen "vk1") ^ ", " ^ (tmp_gen "vk2") ^ ");\n" ^
                       "the_inserted_flow = " ^
                       " flw(flid(isp, dp,\
                        isip, dip, user_buf_23),\n\
                        flid(new_index_2_0, dp, external_ip, dip,\
                        user_buf_23)," ^ !last_device_id ^ ");\n\
                       assert dmap_dchain_coherent(" ^ (tmp_gen "cur_map") ^
                      ", ?ch);\n\
                       flow_id ik = flid(isp, dp,\
                        isip, dip, user_buf_23);\n\
                       coherent_dchain_non_out_of_space_map_nonfull(" ^
                      (tmp_gen "cur_map") ^ ", ch);\n" ^
                      "contains_flow_id_ext_abstract(" ^
                      (tmp_gen "cur_map") ^
                      ", ch, ek);\n" ^
                      "flow the_flow_to_insert = flw(ik, ek," ^ !last_device_id ^ ");\n" ^
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
                          (fun params -> last_device_id := ("(" ^ (List.nth_exn params.args 2) ^ ")->internal_device"); "");
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
     "expire_items", {ret_type = Static Sint32;
                      arg_types = stt [Ptr dchain_struct;
                                   Ptr dmap_struct;
                                   Uint32;];
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
                                   arg_types = stt [Ptr dchain_struct; Ptr Sint32; Uint32;];
                                   extra_ptr_types = [];
                                   lemmas_before = [
                                     capture_chain "cur_ch" 0;
                                   ];
                                   lemmas_after = [
                                     (fun params -> last_device_id := ("(" ^ (List.nth_exn params.args 1) ^ ")->internal_device"); "");
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
                                        "int the_index_allocated = *" ^
                                        (List.nth_exn params.args 1) ^ ";\n");
                                   ];};
     "dchain_rejuvenate_index", {ret_type = Static Sint32;
                                 arg_types = stt [Ptr dchain_struct; Sint32; Uint32;];
                                 extra_ptr_types = [];
                                 lemmas_before = [
                                   capture_chain "cur_ch" 0;
                                   (fun {args;tmp_gen;_} ->
                                      "/*@ {\n\
                                       assert dmap_dchain_coherent(?cur_map, " ^
                                      (tmp_gen "cur_ch") ^
                                      ");\n coherent_same_cap(cur_map, " ^
                                      (tmp_gen "cur_ch") ^ ");\n" ^
                                      "rejuvenate_flow_abstract(cur_map," ^
                                      (tmp_gen "cur_ch") ^ ", " ^
                                      "dmap_get_val_fp(cur_map, " ^
                                      (List.nth_exn args 1) ^ ")," ^
                                      (List.nth_exn args 1) ^ ", " ^
                                      (List.nth_exn args 2) ^ ");\n" ^
                                      "} @*/");
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
                                      "assert dmap_dchain_coherent(?cur_map,?ch);\n" ^
                                      "rejuvenate_preserves_coherent(cur_map, ch, " ^
                                      (List.nth_exn params.args 1) ^ ", "
                                      ^ (List.nth_exn params.args 2) ^ ");\n\
                                       rejuvenate_preserves_index_range(ch," ^
                                      (List.nth_exn params.args 1) ^ ", " ^
                                      (List.nth_exn params.args 2) ^ ");\n}@*/");
                                   (fun params ->
                                      "int the_index_rejuvenated = " ^
                                      (List.nth_exn params.args 1) ^ ";\n");
                                 ];};
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
                 "void to_verify()\n\
                  /*@ requires true; @*/ \n\
                  /*@ ensures true; @*/\n{\n\
                  uint32_t external_ip = 0;\n\
                  uint16_t received_on_port;\n\
                  uint32_t received_packet_type;\n\
                  struct stub_mbuf_content the_received_packet;\n\
                  bool a_packet_received = false;\n\
                  struct stub_mbuf_content sent_packet;\n\
                  uint16_t sent_on_port;\n\
                  uint32_t sent_packet_type;\n\
                  bool a_packet_sent = false;\n"
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

