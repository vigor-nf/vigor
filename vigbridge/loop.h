#ifndef _LOOP_H_INCLUDED_
#define _LOOP_H_INCLUDED_
#include "libvig/verified/double-chain.h"
#include "libvig/verified/map.h"
#include "libvig/verified/vector.h"
#include "libvig/verified/cht.h"
#include "libvig/verified/lpm-dir-24-8.h"
#include "libvig/proof/coherence.h"
#include "libvig/verified/vigor-time.h"
#include "stat_key.h.gen.h"
#include "dyn_value.h.gen.h"
/*@
fixpoint bool dyn_val_conditionl(vigor_time_t t, DynamicValuei v) {
switch(v) {
case DynamicValuec(device):
return (0 <= device) && (device < 2);
}
}

fixpoint bool stat_map_conditionl(vigor_time_t t, pair<StaticKeyi, int> p) {
switch(p) { case pair(value, index):
return switch(value) {
case StaticKeyc(addr, device):
return (0 <= index) && (index < 2);
};
}
}
@*/
/*@
lemma void advance_time_dyn_val_condition(list<pair<DynamicValuei, real> > vec,
vigor_time_t old_time,
vigor_time_t new_time)
requires true == forall(vec, (sup)((dyn_val_conditionl)(old_time), fst)) &*&
old_time <= new_time;
ensures true == forall(vec, (sup)((dyn_val_conditionl)(new_time), fst));
{
switch(vec) {
case nil:
case cons(h,t):
advance_time_dyn_val_condition(t, old_time, new_time);
switch(h) {case pair(v, fr):
switch(v) { case DynamicValuec(device):}
}
}
}

lemma void init_dyn_val_condition(nat cap, vigor_time_t time)
requires 0 <= time;
ensures true == forall(repeat(pair(DEFAULT_DYNAMICVALUE, 1.0), cap), (sup)((dyn_val_conditionl)(time), fst));
{
switch(cap) {
case zero:
case succ(n):
init_dyn_val_condition(n, time);
}
}

lemma void advance_time_stat_map_condition(list<pair<StaticKeyi, int> > map,
vigor_time_t old_time,
vigor_time_t new_time)
requires true == forall(map, (stat_map_conditionl)(old_time)) &*&
old_time <= new_time;
ensures true == forall(map, (stat_map_conditionl)(new_time));
{
switch(map) {
case nil:
case cons(h,t):
advance_time_stat_map_condition(t, old_time, new_time);
switch(h) {case pair(v, fr):
switch(v) { case StaticKeyc(addr, device):}
             }
}
}
@*/
/*@ predicate evproc_loop_invariant(struct Map* dyn_map,
                                    struct Vector* dyn_keys,
                                    struct Vector* dyn_vals,
                                    struct Map* st_map,
                                    struct Vector* st_vec,
                                    struct DoubleChain* dyn_heap,
                                    int capacity,
                                    int stat_capacity,
                                    int dev_count,
                                    unsigned int lcore_id,
                                    vigor_time_t time) = 
              mapp<rte_ether_addri>(dyn_map, rte_ether_addrp, _rte_ether_addr_hash, nop_true, mapc(capacity, ?_dyn_map, ?_dyn_map_addrs)) &*&
              vectorp<rte_ether_addri>(dyn_keys, rte_ether_addrp, ?_dyn_keys, ?_dyn_keys_addrs) &*&
              length(_dyn_keys) == capacity &*&
              vectorp<DynamicValuei>(dyn_vals, DynamicValuep, ?_dyn_vals, ?_dyn_vals_addrs) &*&
              true == forall(_dyn_vals, is_one) &*&
              true == forall(_dyn_vals, (sup)((dyn_val_conditionl)(time), fst)) &*&
              length(_dyn_vals) == capacity &*&
              mapp<StaticKeyi>(st_map, StaticKeyp, _StaticKey_hash, nop_true, mapc(stat_capacity, ?_st_map, ?_st_map_addrs)) &*&
              true == forall(_st_map, (stat_map_conditionl)(time)) &*&
              vectorp<StaticKeyi>(st_vec, StaticKeyp, ?_st_vec, ?_st_vec_addrs) &*&
              true == forall(_st_vec, is_one) &*&
              length(_st_vec) == stat_capacity &*&
              double_chainp(?_dyn_heap, dyn_heap) &*&
              dchain_high_fp(_dyn_heap) <= time &*&
              dchain_index_range_fp(_dyn_heap) == capacity &*&
              capacity < INT_MAX &*&
              stat_capacity < INT_MAX &*&
              dev_count < INT_MAX &*&
              map_vec_chain_coherent<rte_ether_addri>(_dyn_map, _dyn_keys, _dyn_heap) &*&
              true == forall2(_dyn_keys, _dyn_keys_addrs, (kkeeper)(_dyn_map_addrs)) &*&
              lcore_id == 0 &*&
              last_time(time);
@*/
void loop_invariant_consume(struct Map** dyn_map,
                            struct Vector** dyn_keys,
                            struct Vector** dyn_vals,
                            struct Map** st_map,
                            struct Vector** st_vec,
                            struct DoubleChain** dyn_heap,
                            uint32_t capacity,
                            uint32_t stat_capacity,
                            uint32_t dev_count,
                            unsigned int lcore_id,
                            vigor_time_t time);
/*@ requires *dyn_map |-> ?_dyn_map &*& *dyn_keys |-> ?_dyn_keys &*& *dyn_vals |-> ?_dyn_vals &*& *st_map |-> ?_st_map &*& *st_vec |-> ?_st_vec &*& *dyn_heap |-> ?_dyn_heap &*& 
             evproc_loop_invariant(_dyn_map, _dyn_keys, _dyn_vals, _st_map, _st_vec, _dyn_heap, capacity, stat_capacity, dev_count, lcore_id, time); @*/
/*@ ensures *dyn_map |-> _dyn_map &*& *dyn_keys |-> _dyn_keys &*& *dyn_vals |-> _dyn_vals &*& *st_map |-> _st_map &*& *st_vec |-> _st_vec &*& *dyn_heap |-> _dyn_heap &*& true; @*/
void loop_invariant_produce(struct Map** dyn_map,
                            struct Vector** dyn_keys,
                            struct Vector** dyn_vals,
                            struct Map** st_map,
                            struct Vector** st_vec,
                            struct DoubleChain** dyn_heap,
                            uint32_t capacity,
                            uint32_t stat_capacity,
                            uint32_t dev_count,
                            unsigned int* lcore_id,
                            vigor_time_t* time);
/*@ requires *dyn_map |-> ?_dyn_map &*& *dyn_keys |-> ?_dyn_keys &*& *dyn_vals |-> ?_dyn_vals &*& *st_map |-> ?_st_map &*& *st_vec |-> ?_st_vec &*& *dyn_heap |-> ?_dyn_heap &*& *lcore_id |-> _ &*& *time |-> _;@*/
/*@ ensures *dyn_map |-> _dyn_map &*& *dyn_keys |-> _dyn_keys &*& *dyn_vals |-> _dyn_vals &*& *st_map |-> _st_map &*& *st_vec |-> _st_vec &*& *dyn_heap |-> _dyn_heap &*& *lcore_id |-> ?lcid &*& *time |-> ?t &*&
             evproc_loop_invariant(_dyn_map, _dyn_keys, _dyn_vals, _st_map, _st_vec, _dyn_heap, capacity, stat_capacity, dev_count, lcid, t); @*/

void loop_iteration_border(struct Map** dyn_map,
                           struct Vector** dyn_keys,
                           struct Vector** dyn_vals,
                           struct Map** st_map,
                           struct Vector** st_vec,
                           struct DoubleChain** dyn_heap,
                           uint32_t capacity,
                           uint32_t stat_capacity,
                           uint32_t dev_count,
                           unsigned int lcore_id,
                           vigor_time_t time);

#endif//_LOOP_H_INCLUDED_
