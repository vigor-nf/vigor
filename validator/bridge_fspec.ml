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

(* FIXME: borrowed from ../nf/vigbridge/bridge_data_spec.ml*)
let containers = ["dyn_map", Map ("ether_addr", "capacity", "");
                  "dyn_keys", Vector ("ether_addr", "capacity", "");
                  "dyn_vals", Vector ("DynamicValue", "capacity", "dyn_val_condition");
                  "st_map", Map ("StaticKey", "stat_capacity", "stat_map_condition");
                  "st_vec", Vector ("StaticKey", "stat_capacity", "");
                  "dyn_heap", DChain "capacity";
                  "capacity", UInt32;
                  "stat_capacity", UInt32;
                  "dev_count", UInt32;
                  "", EMap ("ether_addr", "dyn_map", "dyn_keys", "dyn_heap")]

let fun_types =
  String.Map.of_alist_exn
    (common_fun_types @
    [(hash_spec ether_addr_struct);
     "loop_invariant_consume", (loop_invariant_consume_spec containers);
     "loop_invariant_produce", (loop_invariant_produce_spec containers);
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
     "map_put", (map_put_spec [("ether_addri","ether_addr","ether_addrp","LMA_ETHER_ADDR",ether_addr_struct,true);
                               ("StaticKeyi","StaticKey","StaticKeyp","LMA_ST_KEY",static_key_struct,false)]);
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
                  //@ int capacity;\n\
                  //@ int stat_capacity;\n\
                  //@ int dev_count;\n\
                  uint16_t received_on_port;\n\
                  int the_index_allocated = -1;\n\
                  int64_t time_for_allocated_index = 0;\n\
                  bool a_packet_received = false;\n\
                  bool is_ipv4 = false;\n\
                  //@ bool packet_is_complete = false;\n\
                  //@ option<void*> last_composed_packet = none;\n\
                  //@ list<uint8_t> last_sent_packet = nil;\n\
                  uint32_t sent_packet_type;\n"
                 ^ "//@ struct Map* dyn_map_ptr;\n"
                 ^ "//@ struct DoubleChain* dyn_heap_ptr;\n"
                 ^ "//@ struct Vector* dyn_vals_ptr;\n"
                 ^ "//@ struct Vector* dyn_keys_ptr;\n"
                 ^ "//@ struct Map* st_map_ptr;\n"
                 ^ "//@ struct Vector* st_vec_ptr;\n"
                 ^ "//@ list<pair<ether_addri, int> > initial_dyn_map;\n"
                 ^ "//@ dchain initial_dyn_heap;\n"
                 ^ "//@ list<pair<DynamicValuei, real> > initial_dyn_vals;\n"
                 ^ "//@ list<pair<ether_addri, real> > initial_dyn_keys;\n"
                 ^ "//@ list<pair<StaticKeyi, int> > initial_st_map;\n"
                 ^ "//@ list<pair<StaticKeyi, real> > initial_st_vec;\n" ^
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

