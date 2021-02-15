#ifndef _LoadBalancedFlow_GEN_H_INCLUDED_
#define _LoadBalancedFlow_GEN_H_INCLUDED_

#include <stdbool.h>
#include "libvig/verified/boilerplate-util.h"

#include "libvig/verified/ether.h"


#include "lb_flow.h"

#define DEFAULT_LOADBALANCEDFLOW LoadBalancedFlowc(0, 0, 0, 0, 0)

/*@
inductive LoadBalancedFlowi = LoadBalancedFlowc(uint32_t , uint32_t , uint16_t , uint16_t , uint8_t ); @*/

/*@
predicate LoadBalancedFlowp(struct LoadBalancedFlow* ptr; LoadBalancedFlowi v) = 
  struct_LoadBalancedFlow_padding(ptr) &*&
  ptr->src_ip |-> ?src_ip_f &*&
  ptr->dst_ip |-> ?dst_ip_f &*&
  ptr->src_port |-> ?src_port_f &*&
  ptr->dst_port |-> ?dst_port_f &*&
  ptr->protocol |-> ?protocol_f &*&
  v == LoadBalancedFlowc(src_ip_f, dst_ip_f, src_port_f, dst_port_f, protocol_f); @*/

/*@
fixpoint unsigned _LoadBalancedFlow_hash(LoadBalancedFlowi x) {
  switch(x) { case LoadBalancedFlowc(src_ip_f, dst_ip_f, src_port_f, dst_port_f, protocol_f):
    return crc32_hash(crc32_hash(crc32_hash(crc32_hash(crc32_hash(0, src_ip_f), dst_ip_f), src_port_f), dst_port_f), protocol_f);
  }
} @*/

unsigned LoadBalancedFlow_hash(void* obj);
//@ requires [?f]LoadBalancedFlowp(obj, ?v);
//@ ensures [f]LoadBalancedFlowp(obj, v) &*& result == _LoadBalancedFlow_hash(v);

bool LoadBalancedFlow_eq(void* a, void* b);
//@ requires [?f1]LoadBalancedFlowp(a, ?aid) &*& [?f2]LoadBalancedFlowp(b, ?bid);
/*@ ensures [f1]LoadBalancedFlowp(a, aid) &*& [f2]LoadBalancedFlowp(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/

void LoadBalancedFlow_allocate(void* obj);
//@ requires chars(obj, sizeof(struct LoadBalancedFlow), _);
//@ ensures LoadBalancedFlowp(obj, DEFAULT_LOADBALANCEDFLOW);

#define LOG_LOADBALANCEDFLOW(obj, p); \
  p("{"); \
  p("src_ip: %d", (obj)->src_ip); \
  p("dst_ip: %d", (obj)->dst_ip); \
  p("src_port: %d", (obj)->src_port); \
  p("dst_port: %d", (obj)->dst_port); \
  p("protocol: %d", (obj)->protocol); \
  p("}");


#ifdef KLEE_VERIFICATION
#  include <klee/klee.h>
#  include "libvig/models/str-descr.h"

extern struct str_field_descr LoadBalancedFlow_descrs[5];
extern struct nested_field_descr LoadBalancedFlow_nests[0];
#endif//KLEE_VERIFICATION

#endif//_LoadBalancedFlow_GEN_H_INCLUDED_
