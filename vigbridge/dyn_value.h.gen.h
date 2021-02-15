#ifndef _DynamicValue_GEN_H_INCLUDED_
#define _DynamicValue_GEN_H_INCLUDED_

#include <stdbool.h>
#include "libvig/verified/boilerplate-util.h"

#include "libvig/verified/ether.h"


#include "dyn_value.h"

#define DEFAULT_DYNAMICVALUE DynamicValuec(0)

/*@
inductive DynamicValuei = DynamicValuec(uint16_t ); @*/

/*@
predicate DynamicValuep(struct DynamicValue* ptr; DynamicValuei v) = 
  struct_DynamicValue_padding(ptr) &*&
  ptr->device |-> ?device_f &*&
  v == DynamicValuec(device_f); @*/

/*@
fixpoint unsigned _DynamicValue_hash(DynamicValuei x) {
  switch(x) { case DynamicValuec(device_f):
    return crc32_hash(0, device_f);
  }
} @*/

unsigned DynamicValue_hash(void* obj);
//@ requires [?f]DynamicValuep(obj, ?v);
//@ ensures [f]DynamicValuep(obj, v) &*& result == _DynamicValue_hash(v);

bool DynamicValue_eq(void* a, void* b);
//@ requires [?f1]DynamicValuep(a, ?aid) &*& [?f2]DynamicValuep(b, ?bid);
/*@ ensures [f1]DynamicValuep(a, aid) &*& [f2]DynamicValuep(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/

void DynamicValue_allocate(void* obj);
//@ requires chars(obj, sizeof(struct DynamicValue), _);
//@ ensures DynamicValuep(obj, DEFAULT_DYNAMICVALUE);

#define LOG_DYNAMICVALUE(obj, p); \
  p("{"); \
  p("device: %d", (obj)->device); \
  p("}");


#ifdef KLEE_VERIFICATION
#  include <klee/klee.h>
#  include "libvig/models/str-descr.h"

extern struct str_field_descr DynamicValue_descrs[1];
extern struct nested_field_descr DynamicValue_nests[0];
#endif//KLEE_VERIFICATION

#endif//_DynamicValue_GEN_H_INCLUDED_
