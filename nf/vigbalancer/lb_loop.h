#ifndef LB_LOOP_H_INCLUDED
#define LB_LOOP_H_INCLUDED

#include "lib/containers/map.h"
#include "lib/containers/vector.h"
#include "lib/containers/double-chain.h"
#include "lib/coherence.h"
#include "lib/nf_time.h"

#include "lb_balancer.h"


/*@
  predicate lb_loop_invariant(struct Map* flow_to_flow_id,
                              struct Vector* flow_heap,
                              struct DoubleChain* flow_chain,
                              struct Vector* flow_id_to_backend_id,
                              struct Vector* backend_ips,
                              struct Vector* backends,
                              struct Map* ip_to_backend_id,
                              struct DoubleChain* active_backends,
                              struct Vector* cht,
                              time_t time, uint32_t backend_capacity, uint32_t flow_capacity) =
          true;
          @*/
/*          mapp<lb_flowi>(indices, lb_flowp, lb_flow_hash_2, nop_true, mapc(flow_capacity, ?indicesi, ?indicesv)) &*&
          vectorp<lb_flowi>(heap, lb_flowp, ?heapv, ?heapa) &*&
          double_chainp(?chainv, chain) &*&
          vectorp<lb_backendi>(backends, lb_backendp, ?backendsv, ?backendsa) &*&
          true == forall2(heapv, heapa, (kkeeper)(indicesv)) &*&
          length(heapv) == flow_capacity &*&
          length(backendsv) == flow_capacity &*&
          map_vec_chain_coherent<lb_flowi>(indicesi, heapv, chainv) &*&
          true == forall(backendsv, is_one) &*&
          last_time(time) &*&
          dchain_high_fp(chainv) <= time;
@*/

void lb_loop_iteration_assumptions(
				struct Map** flow_to_flow_id,
				struct Vector** flow_heap,
				struct DoubleChain** flow_chain,
				struct Vector** flow_id_to_backend_id,
				struct Vector** backend_ips,
				struct Vector** backends,
				struct Map** ip_to_backend_id,
				struct DoubleChain** active_backends,
				struct Vector** cht,
                                   time_t time, uint32_t backend_capacity, uint32_t flow_capacity);

void lb_loop_invariant_consume(
				struct Map** flow_to_flow_id,
				struct Vector** flow_heap,
				struct DoubleChain** flow_chain,
				struct Vector** flow_id_to_backend_id,
				struct Vector** backend_ips,
				struct Vector** backends,
				struct Map** ip_to_backend_id,
				struct DoubleChain** active_backends,
				struct Vector** cht,
                               time_t time, uint32_t backend_capacity, uint32_t flow_capacity);
/*@ requires *flow_to_flow_id |-> ?flow_to_flow_idp &*&
             *flow_heap |-> ?flow_heapp &*&
             *flow_chain |-> ?flow_chainp &*&
             *flow_id_to_backend_id |-> ?flow_id_to_backend_idp &*&
             *backend_ips |-> ?backend_ipsp &*&
             *backends |-> ?backendsp &*&
             *ip_to_backend_id |-> ?ip_to_backend_idp &*&
             *active_backends |-> ?active_backendsp &*&
             *cht |-> ?chtp &*&
             lb_loop_invariant(flow_to_flow_idp, flow_heapp, flow_chainp, flow_id_to_backend_idp, backend_ipsp, backendsp, ip_to_backend_idp, active_backendsp, chtp, time, backend_capacity, flow_capacity); @*/
/*@ ensures *flow_to_flow_id |-> flow_to_flow_idp &*&
            *flow_heap |-> flow_heapp &*&
            *flow_chain |-> flow_chainp &*&
            *flow_id_to_backend_id |-> flow_id_to_backend_idp &*&
            *backend_ips |-> backend_ipsp &*&
            *backends |-> backendsp &*&
            *ip_to_backend_id |-> ip_to_backend_idp &*&
            *active_backends |-> active_backendsp &*&
            *cht |-> chtp; @*/

void lb_loop_invariant_produce(
				struct Map** flow_to_flow_id,
				struct Vector** flow_heap,
				struct DoubleChain** flow_chain,
				struct Vector** flow_id_to_backend_id,
				struct Vector** backend_ips,
				struct Vector** backends,
				struct Map** ip_to_backend_id,
				struct DoubleChain** active_backends,
				struct Vector** cht,
                               time_t* time, uint32_t backend_capacity, uint32_t flow_capacity);
/*@ requires *flow_to_flow_id |-> ?flow_to_flow_idp &*&
             *flow_heap |-> ?flow_heapp &*&
             *flow_chain |-> ?flow_chainp &*&
             *flow_id_to_backend_id |-> ?flow_id_to_backend_idp &*&
             *backend_ips |-> ?backend_ipsp &*&
             *backends |-> ?backendsp &*&
             *ip_to_backend_id |-> ?ip_to_backend_idp &*&
             *active_backends |-> ?active_backendsp &*&
             *cht |-> ?chtp &*&
             *time |-> _; @*/
/*@ ensures *flow_to_flow_id |-> flow_to_flow_idp &*&
            *flow_heap |-> flow_heapp &*&
            *flow_chain |-> flow_chainp &*&
            *flow_id_to_backend_id |-> flow_id_to_backend_idp &*&
            *backend_ips |-> backend_ipsp &*&
            *backends |-> backendsp &*&
            *ip_to_backend_id |-> ip_to_backend_idp &*&
            *active_backends |-> active_backendsp &*&
            *cht |-> chtp  &*&
            *time |-> ?t &*&
            lb_loop_invariant(flow_to_flow_idp, flow_heapp, flow_chainp, flow_id_to_backend_idp, backend_ipsp, backendsp, ip_to_backend_idp, active_backendsp, chtp, t, backend_capacity, flow_capacity); @*/

void lb_loop_iteration_begin(
				struct Map** flow_to_flow_id,
				struct Vector** flow_heap,
				struct DoubleChain** flow_chain,
				struct Vector** flow_id_to_backend_id,
				struct Vector** backend_ips,
				struct Vector** backends,
				struct Map** ip_to_backend_id,
				struct DoubleChain** active_backends,
				struct Vector** cht,
                             time_t time, uint32_t backend_capacity, uint32_t flow_capacity);

void lb_loop_iteration_end(
				struct Map** flow_to_flow_id,
				struct Vector** flow_heap,
				struct DoubleChain** flow_chain,
				struct Vector** flow_id_to_backend_id,
				struct Vector** backend_ips,
				struct Vector** backends,
				struct Map** ip_to_backend_id,
				struct DoubleChain** active_backends,
				struct Vector** cht,
                           time_t time, uint32_t backend_capacity, uint32_t flow_capacity);


#endif // LB_LOOP_H_INCLUDED
