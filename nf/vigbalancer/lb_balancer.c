#include "lb_balancer.h"
#include "lb_state.h"

#include "lib/containers/map.h"
#include "lib/containers/vector.h"
#include "lib/containers/double-chain.h"
#include "lib/expirator.h"

#include <linux/limits.h>
#include <sys/types.h>
#include <rte_ethdev.h>


#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

struct LoadBalancer {
  uint32_t flow_expiration_time;

  uint32_t backend_expiration_time;
  struct State* state;
};

extern struct LoadBalancer* balancer;

bool
lb_backend_id_condition(void* key, int value) {
  return 0 <= value AND value < balancer->state->backend_capacity;
}

bool
lb_flow_id_condition(void* key, int value) {
  return 0 <= value AND value < balancer->state->flow_capacity;
}

bool
lb_backend_condition(void* key, int index, void* state) {
  return 0 < ((struct LoadBalancedBackend*) key)->nic AND
    ((struct LoadBalancedBackend*) key)->nic < rte_eth_dev_count();
}

bool
lb_flow_id2backend_id_cond(void* key, int index, void* state) {
  return *(uint32_t*)key < balancer->state->backend_capacity;
}

struct LoadBalancer*
lb_allocate_balancer(uint32_t flow_capacity, uint32_t backend_capacity,
                     uint32_t cht_height, uint32_t backend_expiration_time,
                     uint32_t flow_expiration_time) {
  struct LoadBalancer* balancer = calloc(1, sizeof(struct LoadBalancer));
  balancer->flow_expiration_time = flow_expiration_time;
  balancer->backend_expiration_time = backend_expiration_time;
  balancer->state = alloc_state(backend_capacity, flow_capacity, cht_height);
  if (balancer->state == NULL) {
    // Don't free anything, exiting.
    return NULL;
  }

  return balancer;
}

struct LoadBalancedBackend
lb_get_backend(struct LoadBalancer* balancer, struct LoadBalancedFlow* flow, vigor_time_t now) {
  int flow_index;
  struct LoadBalancedBackend backend;
  if (map_get(balancer->state->flow_to_flow_id, flow, &flow_index) == 0) {
    int backend_index = 0;
    int found =
      cht_find_preferred_available_backend((uint64_t) LoadBalancedFlow_hash(flow),
                                           balancer->state->cht,
                                           balancer->state->active_backends,
                                           balancer->state->cht_height,
                                           balancer->state->backend_capacity,
                                           &backend_index);
    if (found) {
      if (dchain_allocate_new_index(balancer->state->flow_chain, &flow_index, now) != 0) {
        struct LoadBalancedFlow* vec_flow;
        uint32_t* vec_flow_id_to_backend_id;
        vector_borrow(balancer->state->flow_heap, flow_index, (void**)&vec_flow);
        memcpy(vec_flow, flow, sizeof(struct LoadBalancedFlow));
        vector_borrow(balancer->state->flow_id_to_backend_id, flow_index, (void**)&vec_flow_id_to_backend_id);
        *vec_flow_id_to_backend_id = backend_index;
        vector_return(balancer->state->flow_id_to_backend_id, flow_index, (void*)vec_flow_id_to_backend_id);
        map_put(balancer->state->flow_to_flow_id, vec_flow, flow_index);
        vector_return(balancer->state->flow_heap, flow_index, vec_flow); // other half in map

      }      // Doesn't matter if we can't insert
      struct LoadBalancedBackend* vec_backend;
      vector_borrow(balancer->state->backends, backend_index, (void**)&vec_backend);
      memcpy(&backend, vec_backend, sizeof(struct LoadBalancedBackend));
      vector_return(balancer->state->backends, backend_index, (void*)vec_backend);
    } else {
      //printf("dropping\n");
      // Drop
      backend.nic = 0;// The wan interface.
    }

  } else {
    uint32_t* vec_backend_index;
    vector_borrow(balancer->state->flow_id_to_backend_id, flow_index, (void**)&vec_backend_index);
    uint32_t backend_index = *vec_backend_index;
    vector_return(balancer->state->flow_id_to_backend_id, flow_index, (void*)vec_backend_index);
    if (0 == dchain_is_index_allocated(balancer->state->active_backends, backend_index)) {
      struct LoadBalancedFlow* flow_key;
      //Nevermind the flow_id_to_backend_id, its entry
      // is automatically invalidated, by erasing the map entry.
      vector_borrow(balancer->state->flow_heap, flow_index, (void**)&flow_key);
      // could use `flow_key` just as well here, but
      // current impl of symbex models does not support
      // connecting a map with its keystore.
      map_erase(balancer->state->flow_to_flow_id, flow, (void**)&flow_key);
      dchain_free_index(balancer->state->flow_chain, flow_index);
      vector_return(balancer->state->flow_heap, flow_index, (void*)flow_key);
      return lb_get_backend(balancer, flow, now);
    } else {
      dchain_rejuvenate_index(balancer->state->flow_chain, flow_index, now);

      struct LoadBalancedBackend* vec_backend;
      vector_borrow(balancer->state->backends, backend_index, (void**)&vec_backend);
      memcpy(&backend, vec_backend, sizeof(struct LoadBalancedBackend));
      vector_return(balancer->state->backends, backend_index, (void*)vec_backend);
    }
  }

#ifdef KLEE_VERIFICATION
  // Concretize the backend, to avoid propagating a symbolic device
  concretize_devices(backend.nic, rte_eth_dev_count());
#endif//KLEE_VERIFICATION

  return backend;
}

void lb_process_heartbit(struct LoadBalancer* balancer,
                         struct LoadBalancedFlow* flow,
                         struct ether_addr mac_addr,
                         int nic,
                         vigor_time_t now) {
  int backend_index;
  if (map_get(balancer->state->ip_to_backend_id, &flow->src_ip, &backend_index) == 0) {
    if (0 != dchain_allocate_new_index(balancer->state->active_backends,
                                       &backend_index, now)) {
      struct LoadBalancedBackend* new_backend;
      vector_borrow(balancer->state->backends, backend_index, (void**)&new_backend);
      new_backend->ip = flow->src_ip;
      new_backend->mac = mac_addr;
      new_backend->nic = nic;

      vector_return(balancer->state->backends, backend_index, (void*)new_backend);
      uint32_t* ip;
      vector_borrow(balancer->state->backend_ips, backend_index, (void**)&ip);
      *ip = flow->src_ip;
      map_put(balancer->state->ip_to_backend_id, ip, backend_index);
      vector_return(balancer->state->backend_ips, backend_index, (void*)ip);
    }
    //Otherwise ignore this backend, we are full.
  } else {
    // Removed assert, because it is not trivial to satisfy during symbex
    //assert(dchain_is_index_allocated(balancer->state->active_backends, backend_index));
    dchain_rejuvenate_index(balancer->state->active_backends, backend_index, now);
  }
}

void lb_expire_flows(struct LoadBalancer* balancer, vigor_time_t now) {
  if (now < balancer->flow_expiration_time) return;

  // This is hacky - we want to make sure the sanitization doesn't
  // extend our vigor_time_t value in 128 bits, which would confuse the validator.
  // So we "prove" by hand that it's OK...
  assert(sizeof(int64_t) == sizeof(vigor_time_t));
  if (now < 0) return; // we don't support the past
  uint64_t now_u = (uint64_t) now; // OK since assert above passed and now > 0
  uint64_t last_time_u = now_u - balancer->flow_expiration_time; // OK because now >= flow_expiration_time >= 0
  vigor_time_t last_time = (vigor_time_t) last_time_u; // OK since the assert above passed

  expire_items_single_map(balancer->state->flow_chain, balancer->state->flow_heap, balancer->state->flow_to_flow_id, last_time);
}

void lb_expire_backends(struct LoadBalancer* balancer, vigor_time_t now) {
  if (now < balancer->backend_expiration_time) return;

  // This is hacky - we want to make sure the sanitization doesn't
  // extend our vigor_time_t value in 128 bits, which would confuse the validator.
  // So we "prove" by hand that it's OK...
  assert(sizeof(int64_t) == sizeof(vigor_time_t));
  if (now < 0) return; // we don't support the past
  uint64_t now_u = (uint64_t) now; // OK since assert above passed and now > 0
  uint64_t last_time_u = now_u - balancer->backend_expiration_time; // OK because now >= flow_expiration_time >= 0
  vigor_time_t last_time = (vigor_time_t) last_time_u; // OK since the assert above passed

  expire_items_single_map(balancer->state->active_backends, balancer->state->backend_ips, balancer->state->ip_to_backend_id, last_time);
}
