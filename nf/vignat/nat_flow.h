#ifndef _FLOW_H_INCLUDED_
#define _FLOW_H_INCLUDED_
#include <stdint.h>
#include <stdbool.h>

struct FlowId {
	uint16_t src_port;
	uint16_t dst_port;
	uint32_t src_ip;
	uint32_t dst_ip;
	uint8_t protocol;
};

struct Flow {
	// Some redundancy there, but the double-map assumes the flow contains its IDs
	struct FlowId internal_id;
	struct FlowId external_id;
	uint16_t internal_device;
};

// Logging functions
void flow_log_ip(uint32_t addr);
void flow_log_id(struct FlowId* id);
void flow_log(struct Flow* flow);


#ifdef KLEE_VERIFICATION
#include <klee/klee.h>
#include "lib/stubs/containers/double-map-stub-control.h"

/*
  Metainformation about the structures above. Used for detailed traces in Klee
  symbolic execution engine. See dmap_set_layout in the
  double-map-stub-control.h
 */
extern struct str_field_descr flow_id_descrs[5];
extern struct nested_field_descr flow_nests[10];
extern struct str_field_descr flow_descrs[3];
#endif//KLEE_VERIFICATION

/*@
  inductive flow_id = flid(int, int, int, int, int);
  predicate flow_idp(struct FlowId* idptr; flow_id id) =
    struct_FlowId_padding(idptr) &*&
    idptr->src_port |-> ?sp &*&
    idptr->dst_port |-> ?dp &*&
    idptr->src_ip |-> ?sip &*&
    idptr->dst_ip |-> ?dip &*&
    idptr->protocol |-> ?prot &*&
    id == flid(sp, dp, sip, dip, prot);


  inductive flow = flw(flow_id, flow_id, int);
  predicate flowp(struct Flow* flowptr, flow flow) =
    struct_Flow_padding(flowptr) &*&
    flow_idp(&(flowptr->internal_id), ?iid) &*&
    flow_idp(&(flowptr->external_id), ?eid) &*&
    flowptr->internal_device |-> ?dev &*&
    flow == flw(iid, eid, dev);

  fixpoint long long _wrap(long long x) { return x % INT_MAX; }

  fixpoint unsigned _flow_id_hash(flow_id id) {
    switch(id) {case flid(sp, dp, sip, dip, prot):
                     return _wrap(((((sp * 31) + dp) * 31 + sip) * 31 + dip) * 31 + prot);}
  }

  fixpoint flow_id flow_get_internal_id(flow f) {
    switch(f) { case flw(iid, eid, dev): return iid; }
  }
  fixpoint flow_id flow_get_external_id(flow f) {
    switch(f) { case flw(iid, eid, dev): return eid; }
  }

  fixpoint bool flow_ids_offsets_fp(struct Flow* f, struct FlowId* iid, struct FlowId* eid) {
    return &(f->internal_id) == iid && &(f->external_id) == eid;
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

/**
   Given the flow ID, get the internal and external IDs.
   Necessary for DoubleMap, hence the generalized signature.

   @param flwp - the pointer to the flow.
   @param int_id - the output pointer for the internal ID extracted from the flow.
   @param ext_id - the output pointer for the external ID extracted from the flow.
*/
void flow_extract_keys(void* flow, void** int_id, void** ext_id);
//@ requires [?f]flowp(flow, ?flw) &*& *int_id |-> _ &*& *ext_id |-> _;
/*@ ensures [f]flowp(flow, flw) &*& *int_id |-> ?iidp &*& *ext_id |-> ?eidp &*&
            [f]flow_idp(iidp, ?iid) &*& [f]flow_idp(eidp, ?eid) &*&
            true == flow_ids_offsets_fp(flow, iidp, eidp) &*&
            iid == flow_get_internal_id(flw) &*& eid == flow_get_external_id(flw); @*/

/**
   The opposite of flow_extract_keys.
   Necessary for DoubleMap, hence the generalized signature.

   @param flow - the pointer to the flow.
   @param iidp - pointer to the internal ID, must be the one extracted
                previously.
   @param eidp - pointer to the external ID, must be the one extracted
                previously.
*/
void flow_pack_keys(void* flow, void* iidp, void* eidp);
/*@ requires [?f]flowp(flow, ?flw) &*&
            [f]flow_idp(iidp, ?iid) &*& [f]flow_idp(eidp, ?eid) &*&
            true == flow_ids_offsets_fp(flow, iidp, eidp) &*&
            iid == flow_get_internal_id(flw) &*& eid == flow_get_external_id(flw); @*/
//@ ensures [f]flowp(flow, flw);

/**
   Copy the flow.
   Necessary for DoubleMap, hence the generalized signature.

   @param dst - output pointer for the copy of the flow. Must point to
                a preallocated sufficient memory chunk.
   @param src - the flow to be copied.
*/
void flow_copy(char* dst, void* src);
//@ requires [?f]flowp(src, ?flw) &*& dst[0..sizeof(struct Flow)] |-> _;
//@ ensures [f]flowp(src, flw) &*& flowp((void*) dst, flw);

/**
   Free the resources, acquired by the flow. In practice, does nothing.
   Necessary for DoubleMap, hence the generalized signature.
   It does not free memory itself.

   @param flow - pointer to the flow to be destroyed.
*/
void flow_destroy(void* flow);
//@ requires flowp(flow, _);
//@ ensures chars(flow, sizeof(struct Flow), _);

#endif //_FLOW_H_INCLUDED_
