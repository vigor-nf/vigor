#ifndef _LOOP_H_INCLUDED_
#define _LOOP_H_INCLUDED_
#include "libvig/verified/double-chain.h"
#include "libvig/verified/map.h"
#include "libvig/verified/vector.h"
#include "libvig/verified/cht.h"
#include "libvig/verified/lpm-dir-24-8.h"
#include "libvig/proof/coherence.h"
#include "libvig/verified/vigor-time.h"
#include "ip_addr.h.gen.h"
#include "lb_backend.h.gen.h"
#include "lb_flow.h.gen.h"
/*@
fixpoint bool lb_backend_id_conditionl(vigor_time_t t, pair<ip_addri, int> p) {
switch(p) { case pair(value, index):
return switch(value) {
case ip_addrc(addr):
return (0 <= index) && (index < 32);
};
}
}

fixpoint bool lb_flow_id_conditionl(vigor_time_t t, pair<LoadBalancedFlowi, int> p) {
switch(p) { case pair(value, index):
return switch(value) {
case LoadBalancedFlowc(src_ip, dst_ip, src_port, dst_port, protocol):
return (0 <= index) && (index < 65536);
};
}
}

fixpoint bool lb_backend_conditionl(vigor_time_t t, LoadBalancedBackendi v) {
switch(v) {
case LoadBalancedBackendc(nic, mac, ip):
return (0 <= nic) && (nic < 3) && (nic != 2);
}
}

fixpoint bool lb_flow_id2backend_id_condl(vigor_time_t t, uint32_t v) {
return (v < 32);
}
@*/
/*@
lemma void advance_time_lb_flow_id_condition(list<pair<LoadBalancedFlowi, int> > map,
vigor_time_t old_time,
vigor_time_t new_time)
requires true == forall(map, (lb_flow_id_conditionl)(old_time)) &*&
old_time <= new_time;
ensures true == forall(map, (lb_flow_id_conditionl)(new_time));
{
switch(map) {
case nil:
case cons(h,t):
advance_time_lb_flow_id_condition(t, old_time, new_time);
switch(h) {case pair(v, fr):
switch(v) { case LoadBalancedFlowc(src_ip, dst_ip, src_port, dst_port, protocol):}
             }
}
}

lemma void advance_time_lb_flow_id2backend_id_cond(list<pair<uint32_t, real> > vec,
vigor_time_t old_time,
vigor_time_t new_time)
requires true == forall(vec, (sup)((lb_flow_id2backend_id_condl)(old_time), fst)) &*&
old_time <= new_time;
ensures true == forall(vec, (sup)((lb_flow_id2backend_id_condl)(new_time), fst));
{
switch(vec) {
case nil:
case cons(h,t):
advance_time_lb_flow_id2backend_id_cond(t, old_time, new_time);
switch(h) {case pair(v, fr):
}
}
}

lemma void init_lb_flow_id2backend_id_cond(nat cap, vigor_time_t time)
requires 0 <= time;
ensures true == forall(repeat(pair(DEFAULT_UINT32_T, 1.0), cap), (sup)((lb_flow_id2backend_id_condl)(time), fst));
{
switch(cap) {
case zero:
case succ(n):
init_lb_flow_id2backend_id_cond(n, time);
}
}

lemma void advance_time_lb_backend_id_condition(list<pair<ip_addri, int> > map,
vigor_time_t old_time,
vigor_time_t new_time)
requires true == forall(map, (lb_backend_id_conditionl)(old_time)) &*&
old_time <= new_time;
ensures true == forall(map, (lb_backend_id_conditionl)(new_time));
{
switch(map) {
case nil:
case cons(h,t):
advance_time_lb_backend_id_condition(t, old_time, new_time);
switch(h) {case pair(v, fr):
switch(v) { case ip_addrc(addr):}
             }
}
}

lemma void advance_time_lb_backend_condition(list<pair<LoadBalancedBackendi, real> > vec,
vigor_time_t old_time,
vigor_time_t new_time)
requires true == forall(vec, (sup)((lb_backend_conditionl)(old_time), fst)) &*&
old_time <= new_time;
ensures true == forall(vec, (sup)((lb_backend_conditionl)(new_time), fst));
{
switch(vec) {
case nil:
case cons(h,t):
advance_time_lb_backend_condition(t, old_time, new_time);
switch(h) {case pair(v, fr):
switch(v) { case LoadBalancedBackendc(nic, mac, ip):}
}
}
}

lemma void init_lb_backend_condition(nat cap, vigor_time_t time)
requires 0 <= time;
ensures true == forall(repeat(pair(DEFAULT_LOADBALANCEDBACKEND, 1.0), cap), (sup)((lb_backend_conditionl)(time), fst));
{
switch(cap) {
case zero:
case succ(n):
init_lb_backend_condition(n, time);
}
}
@*/
/*@ predicate evproc_loop_invariant(struct Map* flow_to_flow_id,
                                    struct Vector* flow_heap,
                                    struct DoubleChain* flow_chain,
                                    struct Vector* flow_id_to_backend_id,
                                    struct Map* ip_to_backend_id,
                                    struct Vector* backend_ips,
                                    struct Vector* backends,
                                    struct DoubleChain* active_backends,
                                    struct Vector* cht,
                                    int backend_capacity,
                                    int flow_capacity,
                                    int cht_height,
                                    unsigned int lcore_id,
                                    vigor_time_t time) = 
              mapp<LoadBalancedFlowi>(flow_to_flow_id, LoadBalancedFlowp, _LoadBalancedFlow_hash, nop_true, mapc(flow_capacity, ?_flow_to_flow_id, ?_flow_to_flow_id_addrs)) &*&
              true == forall(_flow_to_flow_id, (lb_flow_id_conditionl)(time)) &*&
              vectorp<LoadBalancedFlowi>(flow_heap, LoadBalancedFlowp, ?_flow_heap, ?_flow_heap_addrs) &*&
              length(_flow_heap) == flow_capacity &*&
              double_chainp(?_flow_chain, flow_chain) &*&
              dchain_high_fp(_flow_chain) <= time &*&
              dchain_index_range_fp(_flow_chain) == flow_capacity &*&
              vectorp<uint32_t>(flow_id_to_backend_id, u_integer, ?_flow_id_to_backend_id, ?_flow_id_to_backend_id_addrs) &*&
              true == forall(_flow_id_to_backend_id, is_one) &*&
              true == forall(_flow_id_to_backend_id, (sup)((lb_flow_id2backend_id_condl)(time), fst)) &*&
              length(_flow_id_to_backend_id) == flow_capacity &*&
              mapp<ip_addri>(ip_to_backend_id, ip_addrp, _ip_addr_hash, nop_true, mapc(backend_capacity, ?_ip_to_backend_id, ?_ip_to_backend_id_addrs)) &*&
              true == forall(_ip_to_backend_id, (lb_backend_id_conditionl)(time)) &*&
              vectorp<ip_addri>(backend_ips, ip_addrp, ?_backend_ips, ?_backend_ips_addrs) &*&
              length(_backend_ips) == backend_capacity &*&
              vectorp<LoadBalancedBackendi>(backends, LoadBalancedBackendp, ?_backends, ?_backends_addrs) &*&
              true == forall(_backends, is_one) &*&
              true == forall(_backends, (sup)((lb_backend_conditionl)(time), fst)) &*&
              length(_backends) == backend_capacity &*&
              double_chainp(?_active_backends, active_backends) &*&
              dchain_high_fp(_active_backends) <= time &*&
              dchain_index_range_fp(_active_backends) == backend_capacity &*&
              vectorp<uint32_t>(cht, u_integer, ?_cht, ?_cht_addrs) &*&
              true == valid_cht(_cht, backend_capacity, cht_height) &*&
              backend_capacity < INT_MAX &*&
              flow_capacity < INT_MAX &*&
              cht_height < INT_MAX &*&
              map_vec_chain_coherent<LoadBalancedFlowi>(_flow_to_flow_id, _flow_heap, _flow_chain) &*&
              true == forall2(_flow_heap, _flow_heap_addrs, (kkeeper)(_flow_to_flow_id_addrs)) &*&
              map_vec_chain_coherent<ip_addri>(_ip_to_backend_id, _backend_ips, _active_backends) &*&
              true == forall2(_backend_ips, _backend_ips_addrs, (kkeeper)(_ip_to_backend_id_addrs)) &*&
              lcore_id == 0 &*&
              last_time(time);
@*/
void loop_invariant_consume(struct Map** flow_to_flow_id,
                            struct Vector** flow_heap,
                            struct DoubleChain** flow_chain,
                            struct Vector** flow_id_to_backend_id,
                            struct Map** ip_to_backend_id,
                            struct Vector** backend_ips,
                            struct Vector** backends,
                            struct DoubleChain** active_backends,
                            struct Vector** cht,
                            uint32_t backend_capacity,
                            uint32_t flow_capacity,
                            uint32_t cht_height,
                            unsigned int lcore_id,
                            vigor_time_t time);
/*@ requires *flow_to_flow_id |-> ?_flow_to_flow_id &*& *flow_heap |-> ?_flow_heap &*& *flow_chain |-> ?_flow_chain &*& *flow_id_to_backend_id |-> ?_flow_id_to_backend_id &*& *ip_to_backend_id |-> ?_ip_to_backend_id &*& *backend_ips |-> ?_backend_ips &*& *backends |-> ?_backends &*& *active_backends |-> ?_active_backends &*& *cht |-> ?_cht &*& 
             evproc_loop_invariant(_flow_to_flow_id, _flow_heap, _flow_chain, _flow_id_to_backend_id, _ip_to_backend_id, _backend_ips, _backends, _active_backends, _cht, backend_capacity, flow_capacity, cht_height, lcore_id, time); @*/
/*@ ensures *flow_to_flow_id |-> _flow_to_flow_id &*& *flow_heap |-> _flow_heap &*& *flow_chain |-> _flow_chain &*& *flow_id_to_backend_id |-> _flow_id_to_backend_id &*& *ip_to_backend_id |-> _ip_to_backend_id &*& *backend_ips |-> _backend_ips &*& *backends |-> _backends &*& *active_backends |-> _active_backends &*& *cht |-> _cht &*& true; @*/
void loop_invariant_produce(struct Map** flow_to_flow_id,
                            struct Vector** flow_heap,
                            struct DoubleChain** flow_chain,
                            struct Vector** flow_id_to_backend_id,
                            struct Map** ip_to_backend_id,
                            struct Vector** backend_ips,
                            struct Vector** backends,
                            struct DoubleChain** active_backends,
                            struct Vector** cht,
                            uint32_t backend_capacity,
                            uint32_t flow_capacity,
                            uint32_t cht_height,
                            unsigned int* lcore_id,
                            vigor_time_t* time);
/*@ requires *flow_to_flow_id |-> ?_flow_to_flow_id &*& *flow_heap |-> ?_flow_heap &*& *flow_chain |-> ?_flow_chain &*& *flow_id_to_backend_id |-> ?_flow_id_to_backend_id &*& *ip_to_backend_id |-> ?_ip_to_backend_id &*& *backend_ips |-> ?_backend_ips &*& *backends |-> ?_backends &*& *active_backends |-> ?_active_backends &*& *cht |-> ?_cht &*& *lcore_id |-> _ &*& *time |-> _;@*/
/*@ ensures *flow_to_flow_id |-> _flow_to_flow_id &*& *flow_heap |-> _flow_heap &*& *flow_chain |-> _flow_chain &*& *flow_id_to_backend_id |-> _flow_id_to_backend_id &*& *ip_to_backend_id |-> _ip_to_backend_id &*& *backend_ips |-> _backend_ips &*& *backends |-> _backends &*& *active_backends |-> _active_backends &*& *cht |-> _cht &*& *lcore_id |-> ?lcid &*& *time |-> ?t &*&
             evproc_loop_invariant(_flow_to_flow_id, _flow_heap, _flow_chain, _flow_id_to_backend_id, _ip_to_backend_id, _backend_ips, _backends, _active_backends, _cht, backend_capacity, flow_capacity, cht_height, lcid, t); @*/

void loop_iteration_border(struct Map** flow_to_flow_id,
                           struct Vector** flow_heap,
                           struct DoubleChain** flow_chain,
                           struct Vector** flow_id_to_backend_id,
                           struct Map** ip_to_backend_id,
                           struct Vector** backend_ips,
                           struct Vector** backends,
                           struct DoubleChain** active_backends,
                           struct Vector** cht,
                           uint32_t backend_capacity,
                           uint32_t flow_capacity,
                           uint32_t cht_height,
                           unsigned int lcore_id,
                           vigor_time_t time);

#endif//_LOOP_H_INCLUDED_
