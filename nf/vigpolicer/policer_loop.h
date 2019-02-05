#ifndef _POLICER_LOOP_H_INCLUDED_
#define _POLICER_LOOP_H_INCLUDED_
#include "lib/containers/double-chain.h"
#include "lib/containers/map.h"
#include "lib/containers/vector.h"
#include "policer_data.h"
#include "lib/coherence.h"
#include "lib/nf_time.h"

/*@
  fixpoint bool st_entry_bound<t>(int bound, pair<t,int> p) {
    return 0 <= snd(p) && snd(p) < bound;
  }

  predicate policer_loop_invariant(struct DoubleChain* dyn_heap,
                                  struct Map* dyn_map,
                                  struct Vector* dyn_keys,
                                  struct Vector* dyn_vals,
                                  struct Map* st_map,
                                  struct Vector* st_vec,
                                  uint32_t capacity,
                                  vigor_time_t time,
                                  uint32_t dev_count) =
    double_chainp(?dh, dyn_heap) &*&
    mapp<ip_addri>(dyn_map, ip_addrp, _ip_addr_hash,
                      nop_true,
                      mapc(capacity, ?dm, ?daddrs)) &*&
    vectorp<ip_addri>(dyn_keys, ip_addrp, ?dks, ?dkaddrs) &*&
    vectorp<uint16_t>(dyn_vals, DynamicValuep, ?dvs, ?dvaddrs) &*&
    true == forall2(dks, dkaddrs, (kkeeper)(daddrs)) &*&
    0 < capacity &*&
    length(dks) == capacity &*&
    length(dvs) == capacity &*&
    true == forall(dvs, is_one) &*&
    map_vec_chain_coherent<ip_addri>(dm, dks, dh) &*&
    dchain_high_fp(dh) <= time &*&
    last_time(time) &*&
    true == forall(sm, (st_entry_bound)(dev_count));

    //TODO: true == forall2(sv, skaddrs, (kkeeper)(saddrs))  ?
    //TODO: true == forall2(dks, dkaddrs, (kkeeper)(daddrs)) ?
  @*/

void policer_loop_invariant_consume(struct DoubleChain** dyn_heap,
                                   struct Map** dyn_map,
                                   struct Vector** dyn_keys,
                                   struct Vector** dyn_vals,
                                   uint32_t capacity,
                                   vigor_time_t time,
                                   uint32_t dev_count);
/*@ requires *dyn_heap |-> ?dh &*&
             *dyn_map |-> ?dm &*&
             *dyn_keys |-> ?dks &*&
             *dyn_vals |-> ?dvs &*&
             *st_map |-> ?sm &*&
             *st_vec |-> ?sv &*&
             policer_loop_invariant(dh, dm, dks, dvs, sm, sv,
                                   capacity, time,
                                   dev_count); @*/
/*@ ensures *dyn_heap |-> dh &*&
            *dyn_map |-> dm &*&
            *dyn_keys |-> dks &*&
            *dyn_vals |-> dvs &*&
            *st_map |-> sm &*&
            *st_vec |-> sv; @*/


void policer_loop_invariant_produce(struct DoubleChain** dyn_heap,
                                   struct Map** dyn_map,
                                   struct Vector** dyn_keys,
                                   struct Vector** dyn_vals,
                                   uint32_t capacity,
                                   vigor_time_t* time,
                                   uint32_t dev_count);
/*@ requires *dyn_heap |-> ?dh &*&
             *dyn_map |-> ?dm &*&
             *dyn_keys |-> ?dks &*&
             *dyn_vals |-> ?dvs &*&
             *st_map |-> ?sm &*&
             *st_vec |-> ?sv &*&
             *time |-> _; @*/
/*@ ensures *dyn_heap |-> dh &*&
            *dyn_map |-> dm &*&
            *dyn_keys |-> dks &*&
            *dyn_vals |-> dvs &*&
            *st_map |-> sm &*&
            *st_vec |-> sv &*&
            *time |-> ?t &*&
            policer_loop_invariant(dh, dm, dks, dvs, sm, sv,
                                  capacity, t,
                                  dev_count); @*/

void policer_loop_iteration_begin(struct DoubleChain** dyn_heap,
                                 struct Map** dyn_map,
                                 struct Vector** dyn_keys,
                                 struct Vector** dyn_vals,
                                 uint32_t capacity,
                                 vigor_time_t time,
                                 uint16_t dev_count);
/*@ requires true; @*/
/*@ ensures true; @*/

void policer_loop_iteration_end(struct DoubleChain** dyn_heap,
                               struct Map** dyn_map,
                               struct Vector** dyn_keys,
                               struct Vector** dyn_vals,
                               uint32_t capacity,
                               vigor_time_t time,
                               uint16_t dev_count);
/*@ requires true; @*/
/*@ ensures true; @*/

void policer_loop_iteration_assumptions(struct DoubleChain** dyn_heap,
                                       struct Map** dyn_map,
                                       struct Vector** dyn_keys,
                                       struct Vector** dyn_vals,
                                       uint32_t capacity,
                                       vigor_time_t time);
/*@ requires true; @*/
/*@ ensures true; @*/

#endif//_POLICER_LOOP_H_INCLUDED_
