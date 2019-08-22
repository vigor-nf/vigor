#include "libvig/verified/ether.h"

bool ether_addr_eq(void* a, void* b)
//@ requires [?f1]ether_addrp(a, ?aid) &*& [?f2]ether_addrp(b, ?bid);
/*@ ensures [f1]ether_addrp(a, aid) &*& [f2]ether_addrp(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/
{
  struct ether_addr* id1 = (struct ether_addr*) a;
  struct ether_addr* id2 = (struct ether_addr*) b;
  //@ open [f1]ether_addrp(a, aid);
  //@ open [f2]ether_addrp(b, bid);
  return (id1->addr_bytes[0] == id2->addr_bytes[0])
     AND (id1->addr_bytes[1] == id2->addr_bytes[1])
     AND (id1->addr_bytes[2] == id2->addr_bytes[2])
     AND (id1->addr_bytes[3] == id2->addr_bytes[3])
     AND (id1->addr_bytes[4] == id2->addr_bytes[4])
     AND (id1->addr_bytes[5] == id2->addr_bytes[5]);
  //@ close [f1]ether_addrp(a, aid);
  //@ close [f2]ether_addrp(b, bid);

}


void ether_addr_allocate(void* obj)
//@ requires chars(obj, sizeof(struct ether_addr), _);
//@ ensures ether_addrp(obj, _);
{
  IGNORE(obj);
  //@ close_struct((struct ether_addr*) obj);
  //@ close ether_addrp(obj, _);
}

#ifdef KLEE_VERIFICATION
struct str_field_descr ether_addr_descrs[] = {
  {offsetof(struct ether_addr, addr_bytes), sizeof(uint8_t ), 6, "addr_bytes"},
};
struct nested_field_descr ether_addr_nests[] = {

};
unsigned ether_addr_hash(void* obj)
{
  klee_trace_ret();
  klee_trace_param_tagged_ptr(obj, sizeof(struct ether_addr),
                             "obj", "ether_addr", TD_BOTH);
  for (int i = 0; i < sizeof(ether_addr_descrs)/sizeof(ether_addr_descrs[0]); ++i) {
    klee_trace_param_ptr_field_arr_directed(obj,
                                            ether_addr_descrs[i].offset,
                                            ether_addr_descrs[i].width,
                                            ether_addr_descrs[i].count,
                                            ether_addr_descrs[i].name,
                                            TD_BOTH);
  }  for (int i = 0; i < sizeof(ether_addr_nests)/sizeof(ether_addr_nests[0]); ++i) {
    klee_trace_param_ptr_nested_field_arr_directed(obj,
                                                  ether_addr_nests[i].base_offset,
                                                  ether_addr_nests[i].offset,
                                                  ether_addr_nests[i].width,
                                                  ether_addr_nests[i].count,
                                                  ether_addr_nests[i].name,
                                                  TD_BOTH);
  }  return klee_int("ether_addr_hash");}

#else//KLEE_VERIFICATION

unsigned ether_addr_hash(void* obj)
//@ requires [?f]ether_addrp(obj, ?v);
//@ ensures [f]ether_addrp(obj, v) &*& result == _ether_addr_hash(v);
{
  struct ether_addr* id = (struct ether_addr*) obj;

  //@ open [f]ether_addrp(obj, v);
  uint8_t addr_bytes_0 = id->addr_bytes[0];
  //@ produce_limits(addr_bytes_0);
  uint8_t addr_bytes_1 = id->addr_bytes[1];
  //@ produce_limits(addr_bytes_1);
  uint8_t addr_bytes_2 = id->addr_bytes[2];
  //@ produce_limits(addr_bytes_2);
  uint8_t addr_bytes_3 = id->addr_bytes[3];
  //@ produce_limits(addr_bytes_3);
  uint8_t addr_bytes_4 = id->addr_bytes[4];
  //@ produce_limits(addr_bytes_4);
  uint8_t addr_bytes_5 = id->addr_bytes[5];
  //@ produce_limits(addr_bytes_5);
  //@ close [f]ether_addrp(obj, v);

  unsigned hash = 0;
  hash = __builtin_ia32_crc32si(hash, addr_bytes_0);
  hash = __builtin_ia32_crc32si(hash, addr_bytes_1);
  hash = __builtin_ia32_crc32si(hash, addr_bytes_2);
  hash = __builtin_ia32_crc32si(hash, addr_bytes_3);
  hash = __builtin_ia32_crc32si(hash, addr_bytes_4);
  hash = __builtin_ia32_crc32si(hash, addr_bytes_5);
  return hash;
}

#endif//KLEE_VERIFICATION
