#include "lb_flow.h.gen.h"

#include <stdint.h>

bool LoadBalancedFlow_eq(void* a, void* b)
//@ requires [?f1]LoadBalancedFlowp(a, ?aid) &*& [?f2]LoadBalancedFlowp(b, ?bid);
/*@ ensures [f1]LoadBalancedFlowp(a, aid) &*& [f2]LoadBalancedFlowp(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/
{
  struct LoadBalancedFlow* id1 = (struct LoadBalancedFlow*) a;
  struct LoadBalancedFlow* id2 = (struct LoadBalancedFlow*) b;
  //@ open [f1]LoadBalancedFlowp(a, aid);
  //@ open [f2]LoadBalancedFlowp(b, bid);
  return (id1->src_ip == id2->src_ip)
     AND (id1->dst_ip == id2->dst_ip)
     AND (id1->src_port == id2->src_port)
     AND (id1->dst_port == id2->dst_port)
     AND (id1->protocol == id2->protocol);
  //@ close [f1]LoadBalancedFlowp(a, aid);
  //@ close [f2]LoadBalancedFlowp(b, bid);

}


void LoadBalancedFlow_allocate(void* obj)
//@ requires chars(obj, sizeof(struct LoadBalancedFlow), _);
//@ ensures LoadBalancedFlowp(obj, DEFAULT_LOADBALANCEDFLOW);
{
  //@ close_struct((struct LoadBalancedFlow*) obj);
  struct LoadBalancedFlow* id = (struct LoadBalancedFlow*) obj;
  id->src_ip = 0;
  id->dst_ip = 0;
  id->src_port = 0;
  id->dst_port = 0;
  id->protocol = 0;
  //@ close LoadBalancedFlowp(obj, DEFAULT_LOADBALANCEDFLOW);
}


#ifdef KLEE_VERIFICATION
struct str_field_descr LoadBalancedFlow_descrs[] = {
  {offsetof(struct LoadBalancedFlow, src_ip), sizeof(uint32_t ), 0, "src_ip"},
  {offsetof(struct LoadBalancedFlow, dst_ip), sizeof(uint32_t ), 0, "dst_ip"},
  {offsetof(struct LoadBalancedFlow, src_port), sizeof(uint16_t ), 0, "src_port"},
  {offsetof(struct LoadBalancedFlow, dst_port), sizeof(uint16_t ), 0, "dst_port"},
  {offsetof(struct LoadBalancedFlow, protocol), sizeof(uint8_t ), 0, "protocol"},
};
struct nested_field_descr LoadBalancedFlow_nests[] = {

};
unsigned LoadBalancedFlow_hash(void* obj)
{
  klee_trace_ret();
  klee_trace_param_tagged_ptr(obj, sizeof(struct LoadBalancedFlow),
                             "obj", "LoadBalancedFlow", TD_BOTH);
  for (int i = 0; i < sizeof(LoadBalancedFlow_descrs)/sizeof(LoadBalancedFlow_descrs[0]); ++i) {
    klee_trace_param_ptr_field_arr_directed(obj,
                                            LoadBalancedFlow_descrs[i].offset,
                                            LoadBalancedFlow_descrs[i].width,
                                            LoadBalancedFlow_descrs[i].count,
                                            LoadBalancedFlow_descrs[i].name,
                                            TD_BOTH);
  }  for (int i = 0; i < sizeof(LoadBalancedFlow_nests)/sizeof(LoadBalancedFlow_nests[0]); ++i) {
    klee_trace_param_ptr_nested_field_arr_directed(obj,
                                                  LoadBalancedFlow_nests[i].base_offset,
                                                  LoadBalancedFlow_nests[i].offset,
                                                  LoadBalancedFlow_nests[i].width,
                                                  LoadBalancedFlow_nests[i].count,
                                                  LoadBalancedFlow_nests[i].name,
                                                  TD_BOTH);
  }  return klee_int("LoadBalancedFlow_hash");}

#else//KLEE_VERIFICATION

unsigned LoadBalancedFlow_hash(void* obj)
//@ requires [?f]LoadBalancedFlowp(obj, ?v);
//@ ensures [f]LoadBalancedFlowp(obj, v) &*& result == _LoadBalancedFlow_hash(v);
{
  struct LoadBalancedFlow* id = (struct LoadBalancedFlow*) obj;

  //@ open [f]LoadBalancedFlowp(obj, v);
  //@ close [f]LoadBalancedFlowp(obj, v);

  unsigned hash = 0;
  hash = __builtin_ia32_crc32si(hash, id->src_ip);
  hash = __builtin_ia32_crc32si(hash, id->dst_ip);
  hash = __builtin_ia32_crc32si(hash, id->src_port);
  hash = __builtin_ia32_crc32si(hash, id->dst_port);
  hash = __builtin_ia32_crc32si(hash, id->protocol);
  return hash;
}

#endif//KLEE_VERIFICATION

