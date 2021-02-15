#ifndef _LoadBalancedBackend_GEN_H_INCLUDED_
#define _LoadBalancedBackend_GEN_H_INCLUDED_

#include <stdbool.h>
#include "libvig/verified/boilerplate-util.h"

#include "libvig/verified/ether.h"


#include "lb_backend.h"

#define DEFAULT_LOADBALANCEDBACKEND LoadBalancedBackendc(0, rte_ether_addrc(0, 0, 0, 0, 0, 0), 0)

/*@
inductive LoadBalancedBackendi = LoadBalancedBackendc(uint16_t , rte_ether_addri, uint32_t ); @*/

/*@
predicate LoadBalancedBackendp(struct LoadBalancedBackend* ptr; LoadBalancedBackendi v) = 
  struct_LoadBalancedBackend_padding(ptr) &*&
  ptr->nic |-> ?nic_f &*&
  rte_ether_addrp(&ptr->mac, ?mac_f) &*&
  ptr->ip |-> ?ip_f &*&
  v == LoadBalancedBackendc(nic_f, mac_f, ip_f); @*/

/*@
fixpoint unsigned _LoadBalancedBackend_hash(LoadBalancedBackendi x) {
  switch(x) { case LoadBalancedBackendc(nic_f, mac_f, ip_f):
    return crc32_hash(crc32_hash(crc32_hash(0, nic_f), _rte_ether_addr_hash(mac_f)), ip_f);
  }
} @*/

unsigned LoadBalancedBackend_hash(void* obj);
//@ requires [?f]LoadBalancedBackendp(obj, ?v);
//@ ensures [f]LoadBalancedBackendp(obj, v) &*& result == _LoadBalancedBackend_hash(v);

bool LoadBalancedBackend_eq(void* a, void* b);
//@ requires [?f1]LoadBalancedBackendp(a, ?aid) &*& [?f2]LoadBalancedBackendp(b, ?bid);
/*@ ensures [f1]LoadBalancedBackendp(a, aid) &*& [f2]LoadBalancedBackendp(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/

void LoadBalancedBackend_allocate(void* obj);
//@ requires chars(obj, sizeof(struct LoadBalancedBackend), _);
//@ ensures LoadBalancedBackendp(obj, DEFAULT_LOADBALANCEDBACKEND);

#define LOG_LOADBALANCEDBACKEND(obj, p); \
  p("{"); \
  p("nic: %d", (obj)->nic); \
  p("mac:"); \
  LOG_RTE_ETHER_ADDR(&(obj)->mac); \
  p("ip: %d", (obj)->ip); \
  p("}");


#ifdef KLEE_VERIFICATION
#  include <klee/klee.h>
#  include "libvig/models/str-descr.h"

extern struct str_field_descr LoadBalancedBackend_descrs[3];
extern struct nested_field_descr LoadBalancedBackend_nests[1];
#endif//KLEE_VERIFICATION

#endif//_LoadBalancedBackend_GEN_H_INCLUDED_
