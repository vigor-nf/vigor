#ifndef LB_LOOP_H_INCLUDED
#define LB_LOOP_H_INCLUDED

#include "lib/containers/map.h"
#include "lib/coherence.h"

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
                              vigor_time_t time,
                              uint32_t backend_capacity,
                              uint32_t flow_capacity,
                              uint32_t cht_height) =
          mapp<LoadBalancedFlowi>(flow_to_flow_id, LoadBalancedFlowp, _LoadBalancedFlow_hash, nop_true, mapc(flow_capacity, ?flow_map, ?flow_mapv)) &*&
          vectorp<LoadBalancedFlowi>(flow_heap, LoadBalancedFlowp, ?flow_vec, ?flow_veca) &*&
          double_chainp(?flow_ch, flow_chain) &*&
          vectorp<uint32_t>(flow_id_to_backend_id, u_integer, ?fidbid_vec, ?fidbid_veca) &*&
          vectorp<ip_addri>(backend_ips, ip_addrp, ?ip_vec, ?ip_veca) &*&
          vectorp<LoadBalancedBackendi>(backends, LoadBalancedBackendp, ?backends_vec, ?backends_veca) &*&
          mapp<ip_addri>(ip_to_backend_id, ip_addrp, _ip_addr_hash, nop_true, mapc(backend_capacity, ?ip_map, ?ip_mapv)) &*&
          double_chainp(?bknd_ch, active_backends) &*&
          vectorp<uint32_t>(cht, u_integer, ?cht_vec, _) &*&
          map_vec_chain_coherent<LoadBalancedFlowi>(flow_map, flow_vec, flow_ch) &*&
          map_vec_chain_coherent<ip_addri>(ip_map, ip_vec, bknd_ch) &*&
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
          true == forall(backends_vec, is_one) &*&
          true == forall(fidbid_vec, is_one) &*&
          true == valid_cht(cht_vec, backend_capacity, cht_height);
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
        vigor_time_t time,
        uint32_t backend_capacity,
        uint32_t flow_capacity,
        uint32_t cht_height);

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
        vigor_time_t time,
        uint32_t backend_capacity,
        uint32_t flow_capacity,
        uint32_t cht_height);
/*@ requires *flow_to_flow_id |-> ?flow_to_flow_idp &*&
             *flow_heap |-> ?flow_heapp &*&
             *flow_chain |-> ?flow_chainp &*&
             *flow_id_to_backend_id |-> ?flow_id_to_backend_idp &*&
             *backend_ips |-> ?backend_ipsp &*&
             *backends |-> ?backendsp &*&
             *ip_to_backend_id |-> ?ip_to_backend_idp &*&
             *active_backends |-> ?active_backendsp &*&
             *cht |-> ?chtp &*&
             lb_loop_invariant(flow_to_flow_idp,
                               flow_heapp,
                               flow_chainp,
                               flow_id_to_backend_idp,
                               backend_ipsp,
                               backendsp,
                               ip_to_backend_idp,
                               active_backendsp,
                               chtp,
                               time,
                               backend_capacity,
                               flow_capacity,
                               cht_height); @*/
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
        vigor_time_t* time,
        uint32_t backend_capacity,
        uint32_t flow_capacity,
        uint32_t cht_height);
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
            lb_loop_invariant(flow_to_flow_idp,
                              flow_heapp,
                              flow_chainp,
                              flow_id_to_backend_idp,
                              backend_ipsp,
                              backendsp,
                              ip_to_backend_idp,
                              active_backendsp,
                              chtp,
                              t,
                              backend_capacity,
                              flow_capacity,
                              cht_height); @*/

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
        vigor_time_t time,
        uint32_t backend_capacity,
        uint32_t flow_capacity,
        uint32_t cht_height);

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
        vigor_time_t time,
        uint32_t backend_capacity,
        uint32_t flow_capacity,
        uint32_t cht_height);


#endif // LB_LOOP_H_INCLUDED
