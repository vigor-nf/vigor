open Str
open Core
open Fspec_api
open Ir
open Common_fspec

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

let lb_flow_struct = Ir.Str ( "LoadBalancedFlow", ["src_ip", Uint32;
                                                   "dst_ip", Uint32;
                                                   "src_port", Uint16;
                                                   "dst_port", Uint16;
                                                   "protocol", Uint8;])
let lb_backend_struct = Ir.Str ( "LoadBalancedBackend", ["nic", Uint16;
                                                         "mac", ether_addr_struct;
                                                         "ip", Uint32])

let ip_addr_struct = Ir.Str("ip_addr", ["addr", Uint32])

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
    (common_fun_types @
     ["LoadBalancedFlow_hash", {ret_type = Static Uint32;
                               arg_types = stt [Ptr lb_flow_struct];
                               extra_ptr_types = [];
                               lemmas_before = [];
                               lemmas_after = [];};
     "loop_invariant_consume", {ret_type = Static Void;
                                arg_types = stt
                                    [Ptr (Ptr map_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr dchain_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr map_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr dchain_struct);
                                     Ptr (Ptr vector_struct);
                                     Uint32;
                                     Uint32;
                                     Uint32;
                                     Uint32;
                                     vigor_time_t];
                                extra_ptr_types = [];
                                lemmas_before = [
                                  (fun {args;_} ->
                                     "/*@ close evproc_loop_invariant(*" ^
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
                                     (List.nth_exn args 12) ^ ", " ^
                                     (List.nth_exn args 13) ^ "); @*/");];
                                lemmas_after = [];};
     "loop_invariant_produce", {ret_type = Static Void;
                                arg_types = stt
                                    [Ptr (Ptr map_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr dchain_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr map_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr dchain_struct);
                                     Ptr (Ptr vector_struct);
                                     Uint32;
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
                                     (List.nth_exn args 2) ^ ", *" ^
                                     (List.nth_exn args 3) ^ ", *" ^
                                     (List.nth_exn args 4) ^ ", *" ^
                                     (List.nth_exn args 5) ^ ", *" ^
                                     (List.nth_exn args 6) ^ ", *" ^
                                     (List.nth_exn args 7) ^ ", *" ^
                                     (List.nth_exn args 8) ^ ", " ^
                                     (List.nth_exn args 9) ^ ", " ^
                                     (List.nth_exn args 10) ^ ", " ^
                                     (List.nth_exn args 11) ^ ", *" ^
                                     (List.nth_exn args 12) ^ ", *" ^
                                     (List.nth_exn args 13) ^ "); @*/");
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
                                     ";\nassert mapp<ip_addri>(" ^ (tmp_gen "arg4bis") ^
                                     ", _, _, _, mapc(_, ?" ^ (tmp_gen "initial_backend_ip_map") ^
                                     ", _));\n" ^
                                     "assert *" ^ (List.nth_exn args 5) ^ " |-> ?" ^ (tmp_gen "arg5bis") ^
                                     ";\nassert vectorp<ip_addri>(" ^ (tmp_gen "arg5bis") ^
                                     ", _, ?" ^ (tmp_gen "initial_ip_veca") ^
                                     ", _);\n" ^
                                     "assert *" ^ (List.nth_exn args 6) ^ " |-> ?" ^ (tmp_gen "arg6bis") ^
                                     ";\nassert vectorp<LoadBalancedBackendi>(" ^ (tmp_gen "arg6bis") ^
                                     ", _, ?" ^ (tmp_gen "initial_backends_veca") ^
                                     ", _);\n" ^
                                     "assert *" ^ (List.nth_exn args 7) ^ " |-> ?" ^ (tmp_gen "arg7bis") ^
                                     ";\nassert double_chainp(?" ^ (tmp_gen "initial_active_backends") ^
                                     ", " ^ (tmp_gen "arg7bis") ^
                                     ");\n" ^
                                     "assert *" ^ (List.nth_exn args 8) ^ " |-> ?" ^ (tmp_gen "arg8bis") ^
                                     ";\nassert vectorp<uint32_t>(" ^ (tmp_gen "arg8bis") ^
                                     ", _, ?" ^ (tmp_gen "initial_cht") ^
                                     ", _);\n" ^
                                     ";\nfidbid_veca_ptr = " ^ (tmp_gen "arg3bis") ^
                                     ";\nbackends_veca_ptr = " ^ (tmp_gen "arg6bis") ^
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
      "dchain_allocate", (dchain_alloc_spec [("65536", Some "LoadBalancedFlowi");
                                             ("20", Some "ip_addri")]);
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
                                          "switch(last_map_accessed) {\n\
                                            case LMA_LB_FLOW:\n\
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
                                          (List.nth_exn args 1) ^ ");\n\
                                                                   break;\n\
                                                                    case LMA_IP_ADDR:\n" ^
                                          "assert map_vec_chain_coherent<\
                                           ip_addri>(?" ^
                                          (tmp_gen "cur_map") ^ ", ?" ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^
                                          ");\n\
                                           mvc_coherent_alloc_is_halfowned<ip_addri>(" ^
                                          (tmp_gen "cur_map") ^ ", " ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^ ", *" ^
                                          (List.nth_exn args 1) ^ ");\n" ^
                                          "break;\n\
                                            default:\n\
                                            assert false;\n\
                                          }\n");
                                   ];};
      "dchain_rejuvenate_index", (dchain_rejuvenate_index_spec ["LoadBalancedFlowi", "LMA_LB_FLOW";
                                                                "ip_addri", "LMA_IP_ADDR"]);

     "dchain_is_index_allocated", dchain_is_index_allocated_spec;
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
     "expire_items_single_map", (expire_items_single_map_spec ["LoadBalancedFlowi";"ip_addri"]);
     "map_allocate", (map_alloc_spec [("LoadBalancedFlowi","LoadBalancedFlowp","LoadBalancedFlow_eq","LoadBalancedFlow_hash","_LoadBalancedFlow_hash");
                                      ("ip_addri","ip_addrp","ip_addr_eq","ip_addr_hash","_ip_addr_hash")]);
     "map_get", (* (map_get_spec [
          *  ("LoadBalancedFlowi","LoadBalancedFlow","LoadBalancedFlowp",lb_flow_struct,(fun name ->
          *      "//@ open [_]LoadBalancedFlowp(" ^ name ^ ", _);\n"),true);
          * ("ip_addri","ip_addr","ip_addrp",ip_addr_struct,
          *  (fun name ->
          *     "//@ open ip_addrp(" ^ name ^ ", _);\n")
          * ,false);]) *)
       {ret_type = Static Sint32;
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
                        last_map_accessed = LMA_LB_FLOW;\n" ^
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
                        last_map_accessed = LMA_IP_ADDR;\n" ^
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
     "map_size", map_size_spec;
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
     "vector_allocate", (vector_alloc_spec [("LoadBalancedFlowi","LoadBalancedFlow","LoadBalancedFlowp","LoadBalancedFlow_allocate",true);
                                            ("uint32_t","uint32_t","u_integer","null_init",false);
                                            ("ip_addri","ip_addr","ip_addrp","ip_addr_allocate",true);
                                            ("LoadBalancedBackendi","LoadBalancedBackend","LoadBalancedBackendp","LoadBalancedBackend_allocate",false);
                                            ("uint32_t","uint32_t","u_integer","null_init",false);]);
     "cht_fill_cht",        {ret_type = Static Void;
                             arg_types = [Static (Ptr vector_struct);
                                          Static Sint32;
                                          Static Sint32];
                             extra_ptr_types = [];
                             lemmas_before = [];
                             lemmas_after = []};
      "vector_borrow", (vector_borrow_spec [
          ("LoadBalancedFlowi","LoadBalancedFlow","LoadBalancedFlowp",(fun name ->
               "//@ open [_]LoadBalancedFlowp(*" ^ name ^ ", _);\n"),lb_flow_struct,true);
          ("uint32_t","uint32_t","u_integer",noop,Uint32,false);
          ("ip_addri","ip_addr","ip_addrp",noop,ip_addr_struct,true);
          ("LoadBalancedBackendi","LoadBalancedBackend","LoadBalancedBackendp",(fun name ->
               "//@ open [_]LoadBalancedBackendp(*" ^ name ^ ", _);\n" ^
               "//@ open [_]ether_addrp(" ^ name ^ "->mac, _);\n"),lb_backend_struct,false);
                                           ("uint32_t","uint32_t","u_integer",noop,Uint32,false);]);
     "vector_return", (vector_return_spec [("LoadBalancedFlowi","LoadBalancedFlow","LoadBalancedFlowp",lb_flow_struct,true);
                                           ("uint32_t","uint32_t","u_integer",Uint32,false);
                                           ("ip_addri","ip_addr","ip_addrp",ip_addr_struct,true);
                                           ("LoadBalancedBackendi","LoadBalancedBackend","LoadBalancedBackendp",lb_backend_struct,false);
                                           ("uint32_t","uint32_t","u_integer",Uint32,false);]);])

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
                 "enum LMA_enum {LMA_LB_FLOW, LMA_IP_ADDR, LMA_INVALID};\n" ^
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
                 ^ "//@ LoadBalancedFlowi last_flow_searched_in_the_map;\n\
                    //@ list<phdr> recv_headers = nil; \n\
                    //@ list<phdr> sent_headers = nil; \n\
                    //@ list<uint16_t> sent_on_ports = nil; \n\
                    //@ assume(sizeof(struct ip_addr) == 4);\n\
                    //@ assume(sizeof(struct ether_hdr) == 14);\n\
                    //@ assume(sizeof(struct tcpudp_hdr) == 4);\n\
                    //@ assume(sizeof(struct ipv4_hdr) == 20);//TODO: handle all this sizeof's explicitly\n\
                 "
                 ^
                 "int vector_allocation_order = 0;\n\
                  int map_allocation_order = 0;\n\
                  int dchain_allocation_order = 0;\n\
                  int expire_items_single_map_order = 0;\n\
                  enum LMA_enum last_map_accessed = LMA_INVALID;\n"
  let fun_types = fun_types
  let boundary_fun = "loop_invariant_produce"
  let finishing_fun = "loop_invariant_consume"
  let eventproc_iteration_begin = "loop_invariant_produce"
  let eventproc_iteration_end = "loop_invariant_consume"
  let user_check_for_complete_iteration = In_channel.read_all "balancer_forwarding_property.tmpl"
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

