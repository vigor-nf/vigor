#ifndef _LOOP_H_INCLUDED_
#define _LOOP_H_INCLUDED_
#include "libvig/verified/double-chain.h"
#include "libvig/verified/map.h"
#include "libvig/verified/vector.h"
#include "libvig/verified/cht.h"
#include "libvig/verified/lpm-dir-24-8.h"
#include "libvig/verified/coherence.h"
#include "libvig/verified/vigor-time.h"
#include "dynamic_value.h.gen.h"
#include "ip_addr.h.gen.h"
/*@
  fixpoint bool dyn_val_conditioni(vigor_time_t t, DynamicValuei dv) {
    switch(dv) {
      case DynamicValuec(bucket_size, bucket_time):
        return 0 <= bucket_time && bucket_time <= t &&
               bucket_size <= 3750000000;
    }
  }
  @*/
/*@
  lemma void advance_time_dyn_val_condition(list<pair<DynamicValuei, real> > vec,
                                            vigor_time_t old_time,
                                            vigor_time_t new_time)
  requires true == forall(vec, (sup)((dyn_val_conditioni)(old_time), fst)) &*&
           old_time <= new_time;
  ensures true == forall(vec, (sup)((dyn_val_conditioni)(new_time), fst));
  {
    switch(vec) {
      case nil:
      case cons(h,t):
        advance_time_dyn_val_condition(t, old_time, new_time);
        switch(h) { case pair(dv, fr):
          switch(dv) { case DynamicValuec(bucket_size, bucket_time):
          }
        }
    }
  }
  @*/
/*@ predicate evproc_loop_invariant(struct Map* dyn_map,
                                    struct Vector* dyn_keys,
                                    struct DoubleChain* dyn_heap,
                                    struct Vector* dyn_vals,
                                    int capacity,
                                    int dev_count,
                                    unsigned int lcore_id,
                                    vigor_time_t time) = 
              mapp<ip_addri>(dyn_map, ip_addrp, _ip_addr_hash, nop_true, mapc(capacity, ?_dyn_map, ?_dyn_map_addrs)) &*&
              vectorp<ip_addri>(dyn_keys, ip_addrp, ?_dyn_keys, ?_dyn_keys_addrs) &*&
              length(_dyn_keys) == capacity &*&
              double_chainp(?_dyn_heap, dyn_heap) &*&
              dchain_high_fp(_dyn_heap) <= time &*&
              dchain_index_range_fp(_dyn_heap) == capacity &*&
              vectorp<DynamicValuei>(dyn_vals, DynamicValuep, ?_dyn_vals, ?_dyn_vals_addrs) &*&
              true == forall(_dyn_vals, is_one) &*&
              true == forall(_dyn_vals, (sup)((dyn_val_conditioni)(time), fst)) &*&
              length(_dyn_vals) == capacity &*&
              capacity < INT_MAX &*&
              dev_count < INT_MAX &*&
              map_vec_chain_coherent<ip_addri>(_dyn_map, _dyn_keys, _dyn_heap) &*&
              true == forall2(_dyn_keys, _dyn_keys_addrs, (kkeeper)(_dyn_map_addrs)) &*&
              lcore_id == 0 &*&
              last_time(time);
@*/
void loop_invariant_consume(struct Map** dyn_map,
                            struct Vector** dyn_keys,
                            struct DoubleChain** dyn_heap,
                            struct Vector** dyn_vals,
                            uint32_t capacity,
                            uint32_t dev_count,
                            unsigned int lcore_id,
                            vigor_time_t time);
/*@ requires *dyn_map |-> ?_dyn_map &*& *dyn_keys |-> ?_dyn_keys &*& *dyn_heap |-> ?_dyn_heap &*& *dyn_vals |-> ?_dyn_vals &*& 
             evproc_loop_invariant(_dyn_map, _dyn_keys, _dyn_heap, _dyn_vals, capacity, dev_count, lcore_id, time); @*/
/*@ ensures *dyn_map |-> _dyn_map &*& *dyn_keys |-> _dyn_keys &*& *dyn_heap |-> _dyn_heap &*& *dyn_vals |-> _dyn_vals &*& true; @*/
void loop_invariant_produce(struct Map** dyn_map,
                            struct Vector** dyn_keys,
                            struct DoubleChain** dyn_heap,
                            struct Vector** dyn_vals,
                            uint32_t capacity,
                            uint32_t dev_count,
                            unsigned int* lcore_id,
                            vigor_time_t* time);
/*@ requires *dyn_map |-> ?_dyn_map &*& *dyn_keys |-> ?_dyn_keys &*& *dyn_heap |-> ?_dyn_heap &*& *dyn_vals |-> ?_dyn_vals &*& *lcore_id |-> _ &*& *time |-> _;@*/
/*@ ensures *dyn_map |-> _dyn_map &*& *dyn_keys |-> _dyn_keys &*& *dyn_heap |-> _dyn_heap &*& *dyn_vals |-> _dyn_vals &*& *lcore_id |-> ?lcid &*& *time |-> ?t &*&
             evproc_loop_invariant(_dyn_map, _dyn_keys, _dyn_heap, _dyn_vals, capacity, dev_count, lcid, t); @*/

void loop_iteration_border(struct Map** dyn_map,
                           struct Vector** dyn_keys,
                           struct DoubleChain** dyn_heap,
                           struct Vector** dyn_vals,
                           uint32_t capacity,
                           uint32_t dev_count,
                           unsigned int lcore_id,
                           vigor_time_t time);

#endif//_LOOP_H_INCLUDED_
