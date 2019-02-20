open Str
open Core
open Fspec_api
open Ir
open Common_fspec

type map_key = Int | Ext

let capture_a_chain name {tmp_gen;_} =
  "//@ assert double_chainp(?" ^ (tmp_gen name) ^", _);\n"

let capture_a_vector t name {tmp_gen;_} =
  "//@ assert vectorp<" ^ t ^ ">(_, _, ?" ^ (tmp_gen name) ^ ", _);\n"

let ip_addr_struct = Ir.Str ( "ip_addr", ["addr", Uint32;])
let dynamic_value_struct = Ir.Str ( "DynamicValue", ["bucket_size", Uint32;
                                                     "bucket_time", vigor_time_t;] )

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
    ["loop_invariant_consume", {ret_type = Static Void;
                                arg_types = stt
                                    [Ptr (Ptr map_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr dchain_struct);
                                     Ptr (Ptr vector_struct);
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
                                     (List.nth_exn args 3) ^ ", " ^
                                     (List.nth_exn args 4) ^ ", " ^
                                     (List.nth_exn args 5) ^ ", " ^
                                     (List.nth_exn args 6) ^ ", " ^
                                     (List.nth_exn args 7) ^ "); @*/");];
                                lemmas_after = [];};
     "loop_invariant_produce", {ret_type = Static Void;
                                arg_types = stt
                                    [Ptr (Ptr map_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr dchain_struct);
                                     Ptr (Ptr vector_struct);
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
                                     (List.nth_exn args 3) ^ ", " ^
                                     (List.nth_exn args 4) ^ ", " ^
                                     (List.nth_exn args 5) ^ ", *" ^
                                     (List.nth_exn args 6) ^ ", *" ^
                                     (List.nth_exn args 7) ^ "); @*/");
                                  (fun {tmp_gen;_} ->
                                     "\n/*@ {\n\
                                      assert mapp<ip_addri>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "dm") ^
                                     ", _));\n\
                                      assert vectorp<ip_addri>(_, _, _, _);\n\
                                      assert vectorp<DynamicValuei>(_, _, ?" ^ (tmp_gen "dv_init") ^
                                     ", _);\n\
                                      assert map_vec_chain_coherent<ip_addri>(" ^
                                     (tmp_gen "dm") ^ ", ?" ^
                                     (tmp_gen "dv") ^ ", ?" ^
                                     (tmp_gen "dh") ^
                                     ");\n\
                                      mvc_coherent_same_len<ip_addri>(" ^ (tmp_gen "dm") ^
                                     ", " ^ (tmp_gen "dv") ^
                                     ", " ^ (tmp_gen "dh") ^
                                     ");\n\
                                      initial_dyn_map = " ^ (tmp_gen "dm") ^
                                     ";\ninitial_dyn_val_vec = " ^ (tmp_gen "dv_init") ^
                                     ";\ninitial_dyn_key_vec = " ^ (tmp_gen "dv") ^
                                     ";\ninitial_chain = " ^ (tmp_gen "dh") ^
                                     ";\n} @*/");
                                ];};
     "dchain_allocate", (dchain_alloc_spec "65536" (Some "ip_addri"));
     "dchain_allocate_new_index", (dchain_allocate_new_index_spec "ip_addri");
     "dchain_rejuvenate_index", (dchain_rejuvenate_index_spec "ip_addri");
     "expire_items_single_map", (expire_items_single_map_spec "ip_addri");
     "map_allocate", (map_alloc_spec "ip_addri" "ip_addrp" "ip_addr_eq" "ip_addr_hash" "_ip_addr_hash");
     "map_get", (map_get_spec "ip_addri" "ip_addrp" ip_addr_struct);
     "map_put", (map_put_spec "ip_addri" "ip_addrp" ip_addr_struct
                   (fun str -> "ip_addrc(" ^ str ^ "->addr)"));
     "vector_allocate", {ret_type = Static Sint32;
                         arg_types = stt [Sint32;
                                          Uint32;
                                          Fptr "vector_init_elem";
                                          Ptr (Ptr vector_struct)];
                         extra_ptr_types = [];
                         lemmas_before = [
                           tx_bl
                             "if (dyn_keys_allocated) {\n\
                              produce_function_pointer_chunk \
                              vector_init_elem<DynamicValuei>(DynamicValue_allocate)\
                              (DynamicValuep, sizeof(struct DynamicValue))(a) \
                              {\
                              call();\
                              }\n\
                              } else {\n\
                              produce_function_pointer_chunk \
                              vector_init_elem<ip_addri>(ip_addr_allocate)\
                              (ip_addrp, sizeof(struct ip_addr))(a) \
                              {\
                              call();\
                              }\n\
                              }";
                         ];
                         lemmas_after = [
                           (fun {tmp_gen;ret_name;_} ->
                              "/*@ if (" ^ ret_name ^
                              " && !dyn_keys_allocated) {\n\
                               assert mapp<ip_addri>(_, _, _, _, mapc(?" ^ (tmp_gen "cap") ^
                              ", ?" ^ (tmp_gen "map") ^
                              ", ?" ^ (tmp_gen "addr_map") ^
                              "));\n\
                               assert vectorp<ip_addri>(_, _, ?" ^ (tmp_gen "dks") ^
                              ", ?" ^ (tmp_gen "dkaddrs") ^
                              ");\n\
                               empty_kkeeper(" ^
                              (tmp_gen "dkaddrs") ^
                              ", " ^ (tmp_gen "dks") ^
                              ", " ^ (tmp_gen "addr_map") ^
                              ", " ^ (tmp_gen "cap") ^ ");\n } @*/");
                           (fun _ ->
                              "if (!dyn_keys_allocated)\ dyn_keys_allocated = true;");];};
     "vector_borrow",      {ret_type = Static Void;
                            arg_types = [Static (Ptr vector_struct);
                                         Static Sint32;
                                         Dynamic ["ip_addr",
                                                  Ptr (Ptr ip_addr_struct);
                                                  "DynamicValue",
                                                  Ptr (Ptr dynamic_value_struct)]];
                            extra_ptr_types = ["borrowed_cell",
                                               Dynamic ["ip_addr",
                                                        Ptr ip_addr_struct;
                                                        "DynamicValue",
                                                        Ptr dynamic_value_struct]];
                            lemmas_before = [
                              (fun {args;arg_types;tmp_gen;_} ->
                                 match List.nth_exn arg_types 2 with
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "ip_addr"->
                                   "/*@ {\n\
                                    close hide_vector<DynamicValuei>(_, _, _, _);\n} @*/\n"
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "DynamicValue"->
                                   "/*@ {\n\
                                    close hide_vector<ip_addri>(_, _, _, _);\n\
                                    assert vectorp<DynamicValuei>(_, _, ?" ^ (tmp_gen "vec") ^ ", _);\n\
                                    forall_mem(nth(" ^ (List.nth_exn args 1) ^ ", " ^ (tmp_gen "vec") ^ "), " ^ (tmp_gen "vec") ^ ", is_one);\n} @*/"
                                 | x -> "Error: unexpected argument type: " ^ (ttype_to_str x))
                            ];
                            lemmas_after = [
                              (fun {arg_types;args;_} ->
                                 match List.nth_exn arg_types 2 with
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "ip_addr"->
                                   "/*@ {\n\
                                    open hide_vector<DynamicValuei>(_, _, _, _);\n} @*/\n\
                                    dyn_ks_borrowed = true;\n" ^
                                   "//@ open ip_addrp(*" ^ (List.nth_exn args 2) ^ ", _);\n"
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "DynamicValue"->
                                   "/*@ {\n\
                                    open hide_vector<ip_addri>(_, _, _, _);\n} @*/\n\
                                    dyn_vs_borrowed = true;"
                                 | x -> "Error: unexpected argument type: " ^ (ttype_to_str x));
                              ];};
     "vector_return",      {ret_type = Static Void;
                            arg_types = [Static (Ptr vector_struct);
                                         Static Sint32;
                                         Dynamic ["ip_addr",
                                                  Ptr ip_addr_struct;
                                                  "DynamicValue",
                                                  Ptr dynamic_value_struct]];
                            extra_ptr_types = [];
                            lemmas_before = [
                              (fun {arg_types;tmp_gen;args;_} ->
                                 match List.nth_exn arg_types 2 with
                                 | Ptr (Str (name, _))
                                   when String.equal name "ip_addr"->
                                   "\n/*@ { \n\
                                    assert vectorp<ip_addri>(_, _, ?vectr, _); \n\
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
                                     when String.equal name "ip_addr" ->
                                     "/*@ {\n\
                                      close hide_vector<DynamicValuei>(_, _, _, _);\n} @*/"
                                   | Ptr (Str (name, _))
                                     when String.equal name "DynamicValue" ->
                                     "/*@ {\n\
                                      close hide_vector<ip_addri>(_, _, _, _);} @*/"
                                   | x -> "Error: unexpected argument type: " ^ (ttype_to_str x));
                            ];
                            lemmas_after = [
                                (fun {arg_types;_} ->
                                   match List.nth_exn arg_types 2 with
                                   | Ptr (Str (name, _))
                                     when String.equal name "ip_addr" ->
                                     "/*@ {\n\
                                      open hide_vector<DynamicValuei>(_, _, _, _);\n} @*/\n\
                                      dyn_ks_borrowed = false;"
                                   | Ptr (Str (name, _))
                                     when String.equal name "DynamicValue" ->
                                     "/*@ {\n\
                                      open hide_vector<ip_addri>(_, _, _, _);} @*/\n\
                                      dyn_vs_borrowed = false;"
                                   | x -> "Error: unexpected argument type: " ^ (ttype_to_str x));
                            ];};])

(* TODO: make external_ip symbolic *)
module Iface : Fspec_api.Spec =
struct
  let preamble = "\
#include \"lib/expirator.h\"\n\
#include \"lib/stubs/time_stub_control.h\"\n\
#include \"lib/containers/map.h\"\n\
#include \"lib/containers/double-chain.h\"\n\
#include \"vigpolicer/policer_loop.h\"\n" ^
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
                 ^ "//@ list<pair<ip_addri, int> > initial_dyn_map;\n"
                 ^ "//@ dchain initial_chain;\n"
                 ^ "//@ list<pair<DynamicValuei, real> > initial_dyn_val_vec;\n"
                 ^ "//@ list<pair<ip_addri, real> > initial_dyn_key_vec;\n"
                 ^ "//@ list<phdr> recv_headers = nil; \n\
                  //@ list<phdr> sent_headers = nil; \n\
                  //@ list<int> sent_on_ports = nil; \n"
                 ^
                 "/*@ //TODO: this hack should be \
                  converted to a system \n\
                  assume(sizeof(struct ip_addr) == 4);\n@*/\n\
                  //@ assume(sizeof(struct ether_hdr) == 14);\n\
                  //@ assume(sizeof(struct ipv4_hdr) == 20);\n\
                  /*@ assume(sizeof(struct DynamicValue) == 16);\n@*/\n"
                 ^
                 "bool dyn_keys_allocated = false;\n"
                 ^
                 "bool dyn_ks_borrowed = false;\n\
                  bool dyn_vs_borrowed = false;\n"
  let fun_types = fun_types
  let boundary_fun = "loop_invariant_produce"
  let finishing_fun = "loop_invariant_consume"
  let eventproc_iteration_begin = "loop_invariant_produce"
  let eventproc_iteration_end = "loop_invariant_consume"
  let user_check_for_complete_iteration = In_channel.read_all "policer_forwarding_property.tmpl"
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

