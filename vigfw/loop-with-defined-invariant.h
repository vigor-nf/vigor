#ifndef _LOOP_H_INCLUDED_
#define _LOOP_H_INCLUDED_
#include "libvig/verified/double-chain.h"
#include "libvig/verified/map.h"
#include "libvig/verified/vector.h"
#include "libvig/verified/cht.h"
#include "libvig/verified/lpm-dir-24-8.h"
#include "libvig/verified/coherence.h"
#include "libvig/verified/vigor-time.h"
#include "flow.h.gen.h"
/*@
  fixpoint bool int_dev_boundsi(uint32_t v) {
    return v < 2 && v != 1;
  }
  @*/
/*@ predicate evproc_loop_invariant(struct Map* fm,
                                    struct Vector* fv,
                                    struct Vector* int_devices,
                                    struct DoubleChain* heap,
                                    int max_flows,
                                    int fw_device,
                                    unsigned int lcore_id,
                                    vigor_time_t time) =
              mapp<FlowIdi>(fm, FlowIdp, _FlowId_hash, nop_true, mapc(max_flows, ?_fm, ?_fm_addrs)) &*&
              vectorp<FlowIdi>(fv, FlowIdp, ?_fv, ?_fv_addrs) &*&
              length(_fv) == max_flows &*&
              vectorp<uint32_t>(int_devices, u_integer, ?_int_devices, ?_int_devices_addrs) &*&
              true == forall(_int_devices, (sup)(int_dev_boundsi, fst)) &*&
              true == forall(_int_devices, is_one) &*&
              length(_int_devices) == max_flows &*&
              double_chainp(?_heap, heap) &*&
              dchain_high_fp(_heap) <= time &*&
              dchain_index_range_fp(_heap) == max_flows &*&
              max_flows < INT_MAX &*&
              fw_device < INT_MAX &*&
              map_vec_chain_coherent<FlowIdi>(_fm, _fv, _heap) &*&
              true == forall2(_fv, _fv_addrs, (kkeeper)(_fm_addrs)) &*&
              lcore_id == 0 &*&
              last_time(time);
@*/
void loop_invariant_consume(struct Map** fm,
                            struct Vector** fv,
                            struct Vector** int_devices,
                            struct DoubleChain** heap,
                            int max_flows,
                            uint32_t fw_device,
                            unsigned int lcore_id,
                            vigor_time_t time);
/*@ requires *fm |-> ?_fm &*& *fv |-> ?_fv &*& *int_devices |-> ?_int_devices &*& *heap |-> ?_heap &*& 
             evproc_loop_invariant(_fm, _fv, _int_devices, _heap, max_flows, fw_device, lcore_id, time); @*/
/*@ ensures *fm |-> _fm &*& *fv |-> _fv &*& *int_devices |-> _int_devices &*& *heap |-> _heap &*& true; @*/
void loop_invariant_produce(struct Map** fm,
                            struct Vector** fv,
                            struct Vector** int_devices,
                            struct DoubleChain** heap,
                            int max_flows,
                            uint32_t fw_device,
                            unsigned int* lcore_id,
                            vigor_time_t* time);
/*@ requires *fm |-> ?_fm &*& *fv |-> ?_fv &*& *int_devices |-> ?_int_devices &*& *heap |-> ?_heap &*& *lcore_id |-> _ &*& *time |-> _;@*/
/*@ ensures *fm |-> _fm &*& *fv |-> _fv &*& *int_devices |-> _int_devices &*& *heap |-> _heap &*& *lcore_id |-> ?lcid &*& *time |-> ?t &*&
             evproc_loop_invariant(_fm, _fv, _int_devices, _heap, max_flows, fw_device, lcid, t); @*/

void loop_iteration_border(struct Map** fm,
                           struct Vector** fv,
                           struct Vector** int_devices,
                           struct DoubleChain** heap,
                           int max_flows,
                           uint32_t fw_device,
                           unsigned int lcore_id,
                           vigor_time_t time);

#endif//_LOOP_H_INCLUDED_
