open Str
open Core
open Fspec_api
open Ir
open Common_fspec

let ip_addr_struct = Ir.Str ( "ip_addr", ["addr", Uint32;])
let dynamic_value_struct = Ir.Str ( "DynamicValue", ["bucket_size", Uint32;
                                                     "bucket_time", vigor_time_t;] )
(* FIXME: borrowed from ../nf/vigpolicer/policer_data_spec.ml *)
let containers = ["dyn_map", Map ("ip_addr", "capacity", "");
                  "dyn_keys", Vector ("ip_addr", "capacity", "");
                  "dyn_heap", DChain "capacity";
                  "dyn_vals", Vector ("DynamicValue", "capacity", "");
                  "capacity", UInt32;
                  "dev_count", UInt32;
                  "", EMap ("ip_addr", "dyn_map", "dyn_keys", "dyn_heap");
                 ]

let fun_types =
  String.Map.of_alist_exn
    (common_fun_types @
    ["loop_invariant_consume", (loop_invariant_consume_spec containers);
     "loop_invariant_produce", (loop_invariant_produce_spec containers);
     "dchain_allocate", (dchain_alloc_spec [("65536",(Some "ip_addri"))]);
     "dchain_allocate_new_index", (dchain_allocate_new_index_spec ["ip_addri", "LMA_IP_ADDR"]);
     "dchain_rejuvenate_index", (dchain_rejuvenate_index_spec ["ip_addri", "LMA_IP_ADDR"]);
     "expire_items_single_map", (expire_items_single_map_spec ["ip_addri"]);
     "map_allocate", (map_alloc_spec [("ip_addri","ip_addrp","ip_addr_eq","ip_addr_hash","_ip_addr_hash")]);
     "map_get", (map_get_spec [("ip_addri","ip_addr","ip_addrp","LMA_IP_ADDR","last_ip_addr_searched_in_the_map",ip_addr_struct,noop,true)]);
     "map_put", (map_put_spec [("ip_addri","ip_addr","ip_addrp","LMA_IP_ADDR",ip_addr_struct,true)]);
     "vector_allocate", (vector_alloc_spec [("ip_addri","ip_addr","ip_addrp","ip_addr_allocate",true);
                                            ("DynamicValuei","DynamicValue","DynamicValuep","DynamicValue_allocate",false);]);
     "vector_borrow",      (vector_borrow_spec [("ip_addri","ip_addr","ip_addrp",noop,ip_addr_struct,true);
                                                ("DynamicValuei","DynamicValue","DynamicValuep",noop,dynamic_value_struct,false);]);
     "vector_return",      (vector_return_spec [("ip_addri","ip_addr","ip_addrp",ip_addr_struct,true);
                                                ("DynamicValuei","DynamicValue","DynamicValuep",dynamic_value_struct,false);]);])

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
                 "enum LMA_enum {LMA_IP_ADDR, LMA_INVALID};\n" ^
                 "void to_verify()\n\
                  /*@ requires true; @*/ \n\
                  /*@ ensures true; @*/\n{\n\
                  //@ int capacity;\n\
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
                 ^ "//@ struct Vector* dyn_keys_ptr;\n"
                 ^ "//@ struct Vector* dyn_vals_ptr;\n"
                 ^ "//@ list<pair<ip_addri, int> > initial_dyn_map;\n"
                 ^ "//@ dchain initial_dyn_heap;\n"
                 ^ "//@ list<pair<DynamicValuei, real> > initial_dyn_vals;\n"
                 ^ "//@ list<pair<ip_addri, real> > initial_dyn_keys;\n"
                 ^ "//@ list<phdr> recv_headers = nil; \n\
                  //@ list<phdr> sent_headers = nil; \n\
                  //@ list<uint16_t> sent_on_ports = nil; \n"
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
                 ^
                 "int vector_allocation_order = 0;\n\
                  int map_allocation_order = 0;\n\
                  int dchain_allocation_order = 0;\n\
                  int expire_items_single_map_order = 0;\n\
                  enum LMA_enum last_map_accessed = LMA_IP_ADDR;\n\
                  ip_addri last_ip_addr_searched_in_the_map;\n"
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

