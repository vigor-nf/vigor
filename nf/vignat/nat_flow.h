#ifndef _FLOW_H_INCLUDED_
#define _FLOW_H_INCLUDED_
#include <stdint.h>
#include <stdbool.h>

struct FlowId {
	uint16_t src_port;
	uint16_t dst_port;
	uint32_t src_ip;
	uint32_t dst_ip;
  uint16_t internal_device;
	uint8_t protocol;//Should be the last to avoid a "padding hole"
};

// Logging function
void flow_log_id(struct FlowId* id);


#ifdef KLEE_VERIFICATION
#include <klee/klee.h>
#include "lib/stubs/containers/str-descr.h"

/*
  Metainformation about the structures above. Used for detailed traces in KLEE
  symbolic execution engine. See dmap_set_layout in the
  double-map-stub-control.h
 */
extern struct str_field_descr flow_id_descrs[6];
#endif//KLEE_VERIFICATION

/*@
  inductive flow_id = flid(int, int, int, int, int, int);
  predicate flow_idp(struct FlowId* idptr; flow_id id) =
    struct_FlowId_padding(idptr) &*&
    idptr->src_port |-> ?sp &*&
    idptr->dst_port |-> ?dp &*&
    idptr->src_ip |-> ?sip &*&
    idptr->dst_ip |-> ?dip &*&
    idptr->internal_device |-> ?idev &*&
    idptr->protocol |-> ?prot &*&
    id == flid(sp, dp, sip, dip, idev, prot);


  fixpoint long long _wrap(long long x) { return x % INT_MAX; }

  fixpoint unsigned _flow_id_hash(flow_id id) {
    switch(id) {case flid(sp, dp, sip, dip, idev, prot):
      return _wrap((((((sp * 31) + dp) * 31 + sip) * 31 + dip) * 31 + prot) * 31 + idev);}
  }
  @*/

/**
  Equality comparison function for the flow IDs.
  Necessary for DoubleMap, hence the generalized signature.
  @param a - pointer to the first ID
  @param b - pointer to second ID
  @returns 1 if *a equals *b; and 1 otherwise.
*/
bool flow_id_eq(void* a, void* b);
//@ requires [?f1]flow_idp(a, ?aid) &*& [?f2]flow_idp(b, ?bid);
//@ ensures [f1]flow_idp(a, aid) &*& [f2]flow_idp(b, bid) &*& (result ? aid == bid : aid != bid);

/**
  Hash function for flow IDs.
  Necessary for DoubleMap, hence the generalized signature.

  @param obj - pointer to the ID.
  @returns integer - a hash computed. For equal values the hash values are
  guaranteed to be equal.
*/
unsigned flow_id_hash(void* obj);
//@ requires [?f]flow_idp(obj, ?id);
//@ ensures [f]flow_idp(obj, id) &*& result == _flow_id_hash(id);

void flow_id_allocate(void* flow_id);
//@ requires chars(flow_id, sizeof(struct FlowId), _);
//@ ensures flow_idp(flow_id, _);

#endif //_FLOW_H_INCLUDED_
