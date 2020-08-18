#ifndef _LOOP_H_INCLUDED_
#define _LOOP_H_INCLUDED_
#include "libvig/verified/double-chain.h"
#include "libvig/verified/map.h"
#include "libvig/verified/vector.h"
#include "libvig/verified/cht.h"
#include "libvig/verified/lpm-dir-24-8.h"
#include "libvig/proof/coherence.h"
#include "libvig/verified/vigor-time.h"
#include "flow.h.gen.h"
/*@
fixpoint bool flow_consistencyl(vigor_time_t t, FlowIdi v) {
switch(v) {
case FlowIdc(src_port, dst_port, src_ip, dst_ip, internal_device, protocol):
return (0 <= internal_device) && (internal_device < 2) && (internal_device != 1);
}
}
@*/
/*@
lemma void advance_time_flow_consistency(list<pair<FlowIdi, real> > vec,
vigor_time_t old_time,
vigor_time_t new_time)
requires true == forall(vec, (sup)((flow_consistencyl)(old_time), fst)) &*&
old_time <= new_time;
ensures true == forall(vec, (sup)((flow_consistencyl)(new_time), fst));
{
switch(vec) {
case nil:
case cons(h,t):
advance_time_flow_consistency(t, old_time, new_time);
switch(h) {case pair(v, fr):
switch(v) { case FlowIdc(src_port, dst_port, src_ip, dst_ip, internal_device, protocol):}
}
}
}

lemma void init_flow_consistency(nat cap, vigor_time_t time)
requires 0 <= time;
ensures true == forall(repeat(pair(DEFAULT_FLOWID, 1.0), cap), (sup)((flow_consistencyl)(time), fst));
{
switch(cap) {
case zero:
case succ(n):
init_flow_consistency(n, time);
}
}
@*/
/*@ predicate evproc_loop_invariant(struct Map* fm,
                                    struct Vector* fv,
                                    struct DoubleChain* heap,
                                    int max_flows,
                                    int start_port,
                                    int ext_ip,
                                    int nat_device,
                                    unsigned int lcore_id,
                                    vigor_time_t time) = 
              mapp<FlowIdi>(fm, FlowIdp, _FlowId_hash, nop_true, mapc(max_flows, ?_fm, ?_fm_addrs)) &*&
              vectorp<FlowIdi>(fv, FlowIdp, ?_fv, ?_fv_addrs) &*&
              true == forall(_fv, (sup)((flow_consistencyl)(time), fst)) &*&
              length(_fv) == max_flows &*&
              double_chainp(?_heap, heap) &*&
              dchain_high_fp(_heap) <= time &*&
              dchain_index_range_fp(_heap) == max_flows &*&
              max_flows < INT_MAX &*&
              start_port < INT_MAX &*&
              ext_ip < INT_MAX &*&
              nat_device < INT_MAX &*&
              map_vec_chain_coherent<FlowIdi>(_fm, _fv, _heap) &*&
              true == forall2(_fv, _fv_addrs, (kkeeper)(_fm_addrs)) &*&
              lcore_id == 0 &*&
              last_time(time);
@*/
void loop_invariant_consume(struct Map** fm,
                            struct Vector** fv,
                            struct DoubleChain** heap,
                            int max_flows,
                            int start_port,
                            uint32_t ext_ip,
                            uint32_t nat_device,
                            unsigned int lcore_id,
                            vigor_time_t time);
/*@ requires *fm |-> ?_fm &*& *fv |-> ?_fv &*& *heap |-> ?_heap &*& 
             evproc_loop_invariant(_fm, _fv, _heap, max_flows, start_port, ext_ip, nat_device, lcore_id, time); @*/
/*@ ensures *fm |-> _fm &*& *fv |-> _fv &*& *heap |-> _heap &*& true; @*/
void loop_invariant_produce(struct Map** fm,
                            struct Vector** fv,
                            struct DoubleChain** heap,
                            int max_flows,
                            int start_port,
                            uint32_t ext_ip,
                            uint32_t nat_device,
                            unsigned int* lcore_id,
                            vigor_time_t* time);
/*@ requires *fm |-> ?_fm &*& *fv |-> ?_fv &*& *heap |-> ?_heap &*& *lcore_id |-> _ &*& *time |-> _;@*/
/*@ ensures *fm |-> _fm &*& *fv |-> _fv &*& *heap |-> _heap &*& *lcore_id |-> ?lcid &*& *time |-> ?t &*&
             evproc_loop_invariant(_fm, _fv, _heap, max_flows, start_port, ext_ip, nat_device, lcid, t); @*/

void loop_iteration_border(struct Map** fm,
                           struct Vector** fv,
                           struct DoubleChain** heap,
                           int max_flows,
                           int start_port,
                           uint32_t ext_ip,
                           uint32_t nat_device,
                           unsigned int lcore_id,
                           vigor_time_t time);

#endif//_LOOP_H_INCLUDED_
