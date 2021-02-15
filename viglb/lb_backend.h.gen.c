#include "lb_backend.h.gen.h"

#include <stdint.h>

bool LoadBalancedBackend_eq(void* a, void* b)
//@ requires [?f1]LoadBalancedBackendp(a, ?aid) &*& [?f2]LoadBalancedBackendp(b, ?bid);
/*@ ensures [f1]LoadBalancedBackendp(a, aid) &*& [f2]LoadBalancedBackendp(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/
{
  struct LoadBalancedBackend* id1 = (struct LoadBalancedBackend*) a;
  struct LoadBalancedBackend* id2 = (struct LoadBalancedBackend*) b;
  //@ open [f1]LoadBalancedBackendp(a, aid);
  //@ open [f2]LoadBalancedBackendp(b, bid);
  bool mac_eq = rte_ether_addr_eq(&id1->mac, &id2->mac);
  return (id1->nic == id2->nic)
     AND mac_eq
     AND (id1->ip == id2->ip);
  //@ close [f1]LoadBalancedBackendp(a, aid);
  //@ close [f2]LoadBalancedBackendp(b, bid);

}


void LoadBalancedBackend_allocate(void* obj)
//@ requires chars(obj, sizeof(struct LoadBalancedBackend), _);
//@ ensures LoadBalancedBackendp(obj, DEFAULT_LOADBALANCEDBACKEND);
{
  //@ close_struct((struct LoadBalancedBackend*) obj);
  struct LoadBalancedBackend* id = (struct LoadBalancedBackend*) obj;
  id->nic = 0;
//@ assert id->mac.addr_bytes[0..6] |-> ?mac_addr_bytes_lst;
/*@   switch(mac_addr_bytes_lst) { case cons(h0, t0):
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
  id->mac.addr_bytes[0] = 0;
  id->mac.addr_bytes[1] = 0;
  id->mac.addr_bytes[2] = 0;
  id->mac.addr_bytes[3] = 0;
  id->mac.addr_bytes[4] = 0;
  id->mac.addr_bytes[5] = 0;

  id->ip = 0;
  //@ close LoadBalancedBackendp(obj, DEFAULT_LOADBALANCEDBACKEND);
}


#ifdef KLEE_VERIFICATION
struct str_field_descr LoadBalancedBackend_descrs[] = {
  {offsetof(struct LoadBalancedBackend, nic), sizeof(uint16_t ), 0, "nic"},
  {offsetof(struct LoadBalancedBackend, mac), sizeof(struct rte_ether_addr ), 0, "mac"},
  {offsetof(struct LoadBalancedBackend, ip), sizeof(uint32_t ), 0, "ip"},
};
struct nested_field_descr LoadBalancedBackend_nests[] = {
  {offsetof(struct LoadBalancedBackend, mac), offsetof(struct rte_ether_addr , addr_bytes), sizeof(uint8_t ), 6, "addr_bytes"},
};
unsigned LoadBalancedBackend_hash(void* obj)
{
  klee_trace_ret();
  klee_trace_param_tagged_ptr(obj, sizeof(struct LoadBalancedBackend),
                             "obj", "LoadBalancedBackend", TD_BOTH);
  for (int i = 0; i < sizeof(LoadBalancedBackend_descrs)/sizeof(LoadBalancedBackend_descrs[0]); ++i) {
    klee_trace_param_ptr_field_arr_directed(obj,
                                            LoadBalancedBackend_descrs[i].offset,
                                            LoadBalancedBackend_descrs[i].width,
                                            LoadBalancedBackend_descrs[i].count,
                                            LoadBalancedBackend_descrs[i].name,
                                            TD_BOTH);
  }  for (int i = 0; i < sizeof(LoadBalancedBackend_nests)/sizeof(LoadBalancedBackend_nests[0]); ++i) {
    klee_trace_param_ptr_nested_field_arr_directed(obj,
                                                  LoadBalancedBackend_nests[i].base_offset,
                                                  LoadBalancedBackend_nests[i].offset,
                                                  LoadBalancedBackend_nests[i].width,
                                                  LoadBalancedBackend_nests[i].count,
                                                  LoadBalancedBackend_nests[i].name,
                                                  TD_BOTH);
  }  return klee_int("LoadBalancedBackend_hash");}

#else//KLEE_VERIFICATION

unsigned LoadBalancedBackend_hash(void* obj)
//@ requires [?f]LoadBalancedBackendp(obj, ?v);
//@ ensures [f]LoadBalancedBackendp(obj, v) &*& result == _LoadBalancedBackend_hash(v);
{
  struct LoadBalancedBackend* id = (struct LoadBalancedBackend*) obj;

  //@ open [f]LoadBalancedBackendp(obj, v);
  //@ close [f]LoadBalancedBackendp(obj, v);

  unsigned hash = 0;
  hash = __builtin_ia32_crc32si(hash, id->nic);
  unsigned mac_hash = rte_ether_addr_hash(&id->mac);
  hash = __builtin_ia32_crc32si(hash, mac_hash);
  hash = __builtin_ia32_crc32si(hash, id->ip);
  return hash;
}

#endif//KLEE_VERIFICATION

