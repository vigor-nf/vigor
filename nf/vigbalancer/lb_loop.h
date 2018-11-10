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
          mapp<lb_flowi>(flow_to_flow_id, lb_flowp, lb_flow_hash_2, nop_true, mapc(flow_capacity, ?flow_map, ?flow_mapv)) &*&
          vectorp<lb_flowi>(flow_heap, lb_flowp, ?flow_vec, ?flow_veca) &*&
          double_chainp(?flow_ch, flow_chain) &*&
          vectorp<uint32_t>(flow_id_to_backend_id, u_integer, ?fidbid_vec, ?fidbid_veca) &*&
          vectorp<uint32_t>(backend_ips, u_integer, ?ip_vec, ?ip_veca) &*&
          vectorp<lb_backendi>(backends, lb_backendp, ?backends_vec, ?backends_veca) &*&
          mapp<uint32_t>(ip_to_backend_id, u_integer, lb_ip_hash_fp, nop_true, mapc(backend_capacity, ?ip_map, ?ip_mapv)) &*&
          double_chainp(?bknd_ch, active_backends) &*&
          vectorp<uint32_t>(cht, u_integer, _, _) &*&
          map_vec_chain_coherent<lb_flowi>(flow_map, flow_vec, flow_ch) &*&
          map_vec_chain_coherent<uint32_t>(ip_map, ip_vec, bknd_ch) &*&
          true == forall2(flow_vec, flow_veca, (kkeeper)(flow_mapv)) &*&
          true == forall2(ip_vec, ip_veca, (kkeeper)(ip_mapv)) &*&
          length(flow_vec) == flow_capacity &*&
          length(fidbid_vec) == flow_capacity &*&
          length(ip_vec) == backend_capacity &*&
          last_time(time) &*&
          dchain_high_fp(flow_ch) <= time &*&
          dchain_high_fp(bknd_ch) <= time &*&
          dchain_index_range_fp(flow_ch) == flow_capacity &*&
          dchain_index_range_fp(bknd_ch) == backend_capacity &*&
          length(backends_vec) == backend_capacity &*&
          true == forall(backends_vec, is_one);
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
