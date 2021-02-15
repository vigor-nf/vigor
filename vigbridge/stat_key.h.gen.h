#ifndef _StaticKey_GEN_H_INCLUDED_
#define _StaticKey_GEN_H_INCLUDED_

#include <stdbool.h>
#include "libvig/verified/boilerplate-util.h"

#include "libvig/verified/ether.h"


#include "stat_key.h"

#define DEFAULT_STATICKEY StaticKeyc(rte_ether_addrc(0, 0, 0, 0, 0, 0), 0)

/*@
inductive StaticKeyi = StaticKeyc(rte_ether_addri, uint16_t ); @*/

/*@
predicate StaticKeyp(struct StaticKey* ptr; StaticKeyi v) = 
  struct_StaticKey_padding(ptr) &*&
  rte_ether_addrp(&ptr->addr, ?addr_f) &*&
  ptr->device |-> ?device_f &*&
  v == StaticKeyc(addr_f, device_f); @*/

/*@
fixpoint unsigned _StaticKey_hash(StaticKeyi x) {
  switch(x) { case StaticKeyc(addr_f, device_f):
    return crc32_hash(crc32_hash(0, _rte_ether_addr_hash(addr_f)), device_f);
  }
} @*/

unsigned StaticKey_hash(void* obj);
//@ requires [?f]StaticKeyp(obj, ?v);
//@ ensures [f]StaticKeyp(obj, v) &*& result == _StaticKey_hash(v);

bool StaticKey_eq(void* a, void* b);
//@ requires [?f1]StaticKeyp(a, ?aid) &*& [?f2]StaticKeyp(b, ?bid);
/*@ ensures [f1]StaticKeyp(a, aid) &*& [f2]StaticKeyp(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/

void StaticKey_allocate(void* obj);
//@ requires chars(obj, sizeof(struct StaticKey), _);
//@ ensures StaticKeyp(obj, DEFAULT_STATICKEY);

#define LOG_STATICKEY(obj, p); \
  p("{"); \
  p("addr:"); \
  LOG_RTE_ETHER_ADDR(&(obj)->addr); \
  p("device: %d", (obj)->device); \
  p("}");


#ifdef KLEE_VERIFICATION
#  include <klee/klee.h>
#  include "libvig/models/str-descr.h"

extern struct str_field_descr StaticKey_descrs[2];
extern struct nested_field_descr StaticKey_nests[1];
#endif//KLEE_VERIFICATION

#endif//_StaticKey_GEN_H_INCLUDED_
