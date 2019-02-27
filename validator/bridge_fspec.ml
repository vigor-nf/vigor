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

let static_key_struct = Ir.Str ( "StaticKey", ["addr", ether_addr_struct;
                                               "device", Uint16] )
let dynamic_value_struct = Ir.Str ( "DynamicValue", ["device", Uint16] )
let ether_hdr_struct = Ir.Str ("ether_hdr", ["d_addr", ether_addr_struct;
                                             "s_addr", ether_addr_struct;
                                             "ether_type", Uint16;])

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
    ["ether_addr_hash", {ret_type = Static Uint32;
                         arg_types = stt [Ptr ether_addr_struct];
                         extra_ptr_types = [];
                         lemmas_before = [];
                         lemmas_after = [
                           (fun {args;_} ->
                              "//@ open ether_addrp(" ^ (List.nth_exn args 0) ^ ", _);\n")];};
     "loop_invariant_consume", {ret_type = Static Void;
                                arg_types = stt
                                    [Ptr (Ptr map_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr map_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr dchain_struct);
                                     Uint32;
                                     Uint32;
                                     Uint32;
                                     Uint32;
                                     Sint64];
                                extra_ptr_types = [];
                                lemmas_before = [
                                  (fun {args;_} ->
                                     "/*@ close evproc_loop_invariant(*" ^
                                     (List.nth_exn args 0) ^ ", *" ^
                                     (List.nth_exn args 1) ^ ", *" ^
                                     (List.nth_exn args 2) ^ ", *" ^
                                     (List.nth_exn args 3) ^ ", *" ^
                                     (List.nth_exn args 4) ^ ", *" ^
                                     (List.nth_exn args 5) ^ ", " ^
                                     (List.nth_exn args 6) ^ ", " ^
                                     (List.nth_exn args 7) ^ ", " ^
                                     (List.nth_exn args 8) ^ ", " ^
                                     (List.nth_exn args 9) ^ ", " ^
                                     (List.nth_exn args 10) ^ "); @*/");];
                                lemmas_after = [];};
     "loop_invariant_produce", {ret_type = Static Void;
                                arg_types = stt
                                    [Ptr (Ptr map_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr map_struct);
                                     Ptr (Ptr vector_struct);
                                     Ptr (Ptr dchain_struct);
                                     Uint32;
                                     Uint32;
                                     Uint32;
                                     Ptr Uint32;
                                     Ptr Sint64];
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
                                     (List.nth_exn args 7) ^ ", " ^
                                     (List.nth_exn args 8) ^ ", *" ^
                                     (List.nth_exn args 9) ^ ", *" ^
                                     (List.nth_exn args 10) ^ "); @*/");
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
     "dchain_allocate", (dchain_alloc_spec [("65536",(Some "ether_addri"))]);
     "dchain_allocate_new_index", (dchain_allocate_new_index_spec ["ether_addri", "LMA_ETHER_ADDR"]);
     "dchain_rejuvenate_index", (dchain_rejuvenate_index_spec ["ether_addri", "LMA_ETHER_ADDR"]);
     "expire_items_single_map", (expire_items_single_map_spec ["ether_addri"; "StaticKeyi"]);
     "map_allocate", (map_alloc_spec [("ether_addri","ether_addrp","ether_addr_eq","ether_addr_hash","_ether_addr_hash");
                                      ("StaticKeyi","StaticKeyp","StaticKey_eq","StaticKey_hash","_StaticKey_hash")]) ;
     "map_get", (map_get_spec [
         ("ether_addri","ether_addr","ether_addrp","LMA_ETHER_ADDR","last_ether_addr_searched_in_the_map",ether_addr_struct,(fun name ->
              "//@ open [_]ether_addrp(" ^ name ^ ", _);\n"),true);
         ("StaticKeyi","StaticKey","StaticKeyp","LMA_ST_KEY","last_st_key_searched_in_the_map",static_key_struct,
          (fun name ->
             "//@ open StaticKeyp(" ^ name ^ ", _);\n" ^
             "//@ open ether_addrp(" ^ name ^ ".addr, _);\n")
          ,false);]);
     "map_put", (map_put_spec [("ether_addri","ether_addr","ether_addrp","LMA_ETHER_ADDR",ether_addr_struct,
                                (fun str -> "ether_addrc(" ^ str ^ "->addr_bytes[0], " ^
                                            str ^ "->addr_bytes[1], " ^
                                            str ^ "->addr_bytes[2], " ^
                                            str ^ "->addr_bytes[3], " ^
                                            str ^ "->addr_bytes[4], " ^
                                            str ^ "->addr_bytes[5])"),true);
                               ("StaticKeyi","StaticKey","StaticKeyp","LMA_ST_KEY",static_key_struct,
                                (fun str -> "not needed"),false)]);
     "vector_allocate", (vector_alloc_spec [("ether_addri","ether_addr","ether_addrp","ether_addr_allocate",true);
                                            ("DynamicValuei","DynamicValue","DynamicValuep","DynamicValue_allocate",false);
                                            ("StaticKeyi","StaticKey","StaticKeyp","StaticKey_allocate",true);]);
     "vector_borrow", (vector_borrow_spec [
         ("ether_addri","ether_addr","ether_addrp",(fun name ->
              "//@ open [_]ether_addrp(*" ^ name ^ ", _);\n"),ether_addr_struct,true);
         ("DynamicValuei","DynamicValue","DynamicValuep",noop,dynamic_value_struct,false);
         ("StaticKeyi","StaticKey","StaticKeyp",noop,static_key_struct,true);]) ;
     "vector_return", (vector_return_spec [("ether_addri","ether_addr","ether_addrp",ether_addr_struct,true);
                                           ("DynamicValuei","DynamicValue","DynamicValuep",dynamic_value_struct,false);
                                           ("StaticKeyi","StaticKey","StaticKeyp",static_key_struct,true);]);])

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
                 "enum LMA_enum {LMA_ETHER_ADDR, LMA_ST_KEY, LMA_INVALID};\n" ^
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
                  //@ list<uint16_t> sent_on_ports = nil; \n"
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
                 "int vector_allocation_order = 0;\n\
                  int map_allocation_order = 0;\n\
                  int dchain_allocation_order = 0;\n\
                  int expire_items_single_map_order = 0;\n\
                  enum LMA_enum last_map_accessed = LMA_INVALID;\n\
                  ether_addri last_ether_addr_searched_in_the_map;\n\
                  StaticKeyi last_st_key_searched_in_the_map;\n"
  let fun_types = fun_types
  let boundary_fun = "loop_invariant_produce"
  let finishing_fun = "loop_invariant_consume"
  let eventproc_iteration_begin = "loop_invariant_produce"
  let eventproc_iteration_end = "loop_invariant_consume"
  let user_check_for_complete_iteration = In_channel.read_all "bridge_forwarding_property.tmpl"
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

