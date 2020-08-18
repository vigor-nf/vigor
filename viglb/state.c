#include "state.h"
#include <stdlib.h>
#include "libvig/verified/boilerplate-util.h"
#ifdef KLEE_VERIFICATION
#include "libvig/models/verified/double-chain-control.h"
#include "libvig/models/verified/ether.h"
#include "libvig/models/verified/map-control.h"
#include "libvig/models/verified/vector-control.h"
#include "libvig/models/verified/lpm-dir-24-8-control.h"
#endif//KLEE_VERIFICATION
struct State* allocated_nf_state = NULL;
bool lb_backend_id_condition(void* value, int index, void* state) {
  struct ip_addr *v = value;
  return (0 <= index) AND
        (index < 32);
}
bool lb_flow_id_condition(void* value, int index, void* state) {
  struct LoadBalancedFlow *v = value;
  return (0 <= index) AND
        (index < 65536);
}
bool lb_backend_condition(void* value, int index, void* state) {
  struct LoadBalancedBackend *v = value;
  return (0 <= v->nic) AND
        (v->nic < 3) AND
        (v->nic != 2);
}
bool lb_flow_id2backend_id_cond(void* value, int index, void* state) {
  uint32_t v = *(uint32_t*)value;
  return (v < 32);
}
struct State* alloc_state(uint32_t backend_capacity, uint32_t flow_capacity, uint32_t cht_height)
{
  if (allocated_nf_state != NULL) return allocated_nf_state;
  struct State* ret = malloc(sizeof(struct State));
  if (ret == NULL) return NULL;
  ret->flow_to_flow_id = NULL;
  if (map_allocate(LoadBalancedFlow_eq, LoadBalancedFlow_hash, flow_capacity, &(ret->flow_to_flow_id)) == 0) return NULL;
  ret->flow_heap = NULL;
  if (vector_allocate(sizeof(struct LoadBalancedFlow), flow_capacity, LoadBalancedFlow_allocate, &(ret->flow_heap)) == 0) return NULL;
  ret->flow_chain = NULL;
  if (dchain_allocate(flow_capacity, &(ret->flow_chain)) == 0) return NULL;
  ret->flow_id_to_backend_id = NULL;
  if (vector_allocate(sizeof(uint32_t), flow_capacity, null_init, &(ret->flow_id_to_backend_id)) == 0) return NULL;
  ret->ip_to_backend_id = NULL;
  if (map_allocate(ip_addr_eq, ip_addr_hash, backend_capacity, &(ret->ip_to_backend_id)) == 0) return NULL;
  ret->backend_ips = NULL;
  if (vector_allocate(sizeof(struct ip_addr), backend_capacity, ip_addr_allocate, &(ret->backend_ips)) == 0) return NULL;
  ret->backends = NULL;
  if (vector_allocate(sizeof(struct LoadBalancedBackend), backend_capacity, LoadBalancedBackend_allocate, &(ret->backends)) == 0) return NULL;
  ret->active_backends = NULL;
  if (dchain_allocate(backend_capacity, &(ret->active_backends)) == 0) return NULL;
  ret->cht = NULL;
  if (vector_allocate(sizeof(uint32_t), backend_capacity*cht_height, null_init, &(ret->cht)) == 0) return NULL;
    if (cht_fill_cht(ret->cht, cht_height, backend_capacity) == 0) return NULL;
  ret->backend_capacity = backend_capacity;
  ret->flow_capacity = flow_capacity;
  ret->cht_height = cht_height;
#ifdef KLEE_VERIFICATION
  map_set_layout(ret->flow_to_flow_id, LoadBalancedFlow_descrs, sizeof(LoadBalancedFlow_descrs)/sizeof(LoadBalancedFlow_descrs[0]), LoadBalancedFlow_nests, sizeof(LoadBalancedFlow_nests)/sizeof(LoadBalancedFlow_nests[0]), "LoadBalancedFlow");
  map_set_entry_condition(ret->flow_to_flow_id, lb_flow_id_condition, ret);
  vector_set_layout(ret->flow_heap, LoadBalancedFlow_descrs, sizeof(LoadBalancedFlow_descrs)/sizeof(LoadBalancedFlow_descrs[0]), LoadBalancedFlow_nests, sizeof(LoadBalancedFlow_nests)/sizeof(LoadBalancedFlow_nests[0]), "LoadBalancedFlow");
  vector_set_layout(ret->flow_id_to_backend_id, NULL, 0, NULL, 0, "uint32_t");
  vector_set_entry_condition(ret->flow_id_to_backend_id, lb_flow_id2backend_id_cond, ret);
  map_set_layout(ret->ip_to_backend_id, ip_addr_descrs, sizeof(ip_addr_descrs)/sizeof(ip_addr_descrs[0]), ip_addr_nests, sizeof(ip_addr_nests)/sizeof(ip_addr_nests[0]), "ip_addr");
  map_set_entry_condition(ret->ip_to_backend_id, lb_backend_id_condition, ret);
  vector_set_layout(ret->backend_ips, ip_addr_descrs, sizeof(ip_addr_descrs)/sizeof(ip_addr_descrs[0]), ip_addr_nests, sizeof(ip_addr_nests)/sizeof(ip_addr_nests[0]), "ip_addr");
  vector_set_layout(ret->backends, LoadBalancedBackend_descrs, sizeof(LoadBalancedBackend_descrs)/sizeof(LoadBalancedBackend_descrs[0]), LoadBalancedBackend_nests, sizeof(LoadBalancedBackend_nests)/sizeof(LoadBalancedBackend_nests[0]), "LoadBalancedBackend");
  vector_set_entry_condition(ret->backends, lb_backend_condition, ret);
  vector_set_layout(ret->cht, NULL, 0, NULL, 0, "uint32_t");
#endif//KLEE_VERIFICATION
  allocated_nf_state = ret;
  return ret;
}

#ifdef KLEE_VERIFICATION
void nf_loop_iteration_border(unsigned lcore_id, vigor_time_t time) {
  loop_iteration_border(&allocated_nf_state->flow_to_flow_id,
                        &allocated_nf_state->flow_heap,
                        &allocated_nf_state->flow_chain,
                        &allocated_nf_state->flow_id_to_backend_id,
                        &allocated_nf_state->ip_to_backend_id,
                        &allocated_nf_state->backend_ips,
                        &allocated_nf_state->backends,
                        &allocated_nf_state->active_backends,
                        &allocated_nf_state->cht,
                        allocated_nf_state->backend_capacity,
                        allocated_nf_state->flow_capacity,
                        allocated_nf_state->cht_height,
                        lcore_id,
                        time);
}

#endif//KLEE_VERIFICATION
