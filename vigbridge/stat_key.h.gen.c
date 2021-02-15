#include "stat_key.h.gen.h"

#include <stdint.h>

bool StaticKey_eq(void* a, void* b)
//@ requires [?f1]StaticKeyp(a, ?aid) &*& [?f2]StaticKeyp(b, ?bid);
/*@ ensures [f1]StaticKeyp(a, aid) &*& [f2]StaticKeyp(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/
{
  struct StaticKey* id1 = (struct StaticKey*) a;
  struct StaticKey* id2 = (struct StaticKey*) b;
  //@ open [f1]StaticKeyp(a, aid);
  //@ open [f2]StaticKeyp(b, bid);
  bool addr_eq = rte_ether_addr_eq(&id1->addr, &id2->addr);
  return addr_eq
     AND (id1->device == id2->device);
  //@ close [f1]StaticKeyp(a, aid);
  //@ close [f2]StaticKeyp(b, bid);

}


void StaticKey_allocate(void* obj)
//@ requires chars(obj, sizeof(struct StaticKey), _);
//@ ensures StaticKeyp(obj, DEFAULT_STATICKEY);
{
  //@ close_struct((struct StaticKey*) obj);
  struct StaticKey* id = (struct StaticKey*) obj;
//@ assert id->addr.addr_bytes[0..6] |-> ?addr_addr_bytes_lst;
/*@   switch(addr_addr_bytes_lst) { case cons(h0, t0):
  switch(t0) { case cons(h1, t1):
  switch(t1) { case cons(h2, t2):
  switch(t2) { case cons(h3, t3):
  switch(t3) { case cons(h4, t4):
  switch(t4) { case cons(h5, t5):

  case nil: assert false;
 }
  case nil: assert false;
 }
  case nil: assert false;
 }
  case nil: assert false;
 }
  case nil: assert false;
 }
  case nil: assert false;
 }@*/
  id->addr.addr_bytes[0] = 0;
  id->addr.addr_bytes[1] = 0;
  id->addr.addr_bytes[2] = 0;
  id->addr.addr_bytes[3] = 0;
  id->addr.addr_bytes[4] = 0;
  id->addr.addr_bytes[5] = 0;

  id->device = 0;
  //@ close StaticKeyp(obj, DEFAULT_STATICKEY);
}


#ifdef KLEE_VERIFICATION
struct str_field_descr StaticKey_descrs[] = {
  {offsetof(struct StaticKey, addr), sizeof(struct rte_ether_addr ), 0, "addr"},
  {offsetof(struct StaticKey, device), sizeof(uint16_t ), 0, "device"},
};
struct nested_field_descr StaticKey_nests[] = {
  {offsetof(struct StaticKey, addr), offsetof(struct rte_ether_addr , addr_bytes), sizeof(uint8_t ), 6, "addr_bytes"},
};
unsigned StaticKey_hash(void* obj)
{
  klee_trace_ret();
  klee_trace_param_tagged_ptr(obj, sizeof(struct StaticKey),
                             "obj", "StaticKey", TD_BOTH);
  for (int i = 0; i < sizeof(StaticKey_descrs)/sizeof(StaticKey_descrs[0]); ++i) {
    klee_trace_param_ptr_field_arr_directed(obj,
                                            StaticKey_descrs[i].offset,
                                            StaticKey_descrs[i].width,
                                            StaticKey_descrs[i].count,
                                            StaticKey_descrs[i].name,
                                            TD_BOTH);
  }  for (int i = 0; i < sizeof(StaticKey_nests)/sizeof(StaticKey_nests[0]); ++i) {
    klee_trace_param_ptr_nested_field_arr_directed(obj,
                                                  StaticKey_nests[i].base_offset,
                                                  StaticKey_nests[i].offset,
                                                  StaticKey_nests[i].width,
                                                  StaticKey_nests[i].count,
                                                  StaticKey_nests[i].name,
                                                  TD_BOTH);
  }  return klee_int("StaticKey_hash");}

#else//KLEE_VERIFICATION

unsigned StaticKey_hash(void* obj)
//@ requires [?f]StaticKeyp(obj, ?v);
//@ ensures [f]StaticKeyp(obj, v) &*& result == _StaticKey_hash(v);
{
  struct StaticKey* id = (struct StaticKey*) obj;

  //@ open [f]StaticKeyp(obj, v);
  //@ close [f]StaticKeyp(obj, v);

  unsigned hash = 0;
  unsigned addr_hash = rte_ether_addr_hash(&id->addr);
  hash = __builtin_ia32_crc32si(hash, addr_hash);
  hash = __builtin_ia32_crc32si(hash, id->device);
  return hash;
}

#endif//KLEE_VERIFICATION

