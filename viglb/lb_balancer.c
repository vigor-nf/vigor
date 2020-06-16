#include "lb_balancer.h"
#include "state.h"

#include "libvig/verified/map.h"
#include "libvig/verified/expirator.h"

#include <rte_ethdev.h>

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

struct LoadBalancer {
  vigor_time_t flow_expiration_time;

  vigor_time_t backend_expiration_time;
  struct State *state;
};

struct LoadBalancer *lb_allocate_balancer(uint32_t flow_capacity,
                                          uint32_t backend_capacity,
                                          uint32_t cht_height,
                                          vigor_time_t backend_expiration_time,
                                          vigor_time_t flow_expiration_time) {
  struct LoadBalancer *balancer = calloc(1, sizeof(struct LoadBalancer));
  balancer->flow_expiration_time = flow_expiration_time;
  balancer->backend_expiration_time = backend_expiration_time;
  balancer->state = alloc_state(backend_capacity, flow_capacity, cht_height);
  if (balancer->state == NULL) {
    // Don't free anything, exiting.
    return NULL;
  }

  return balancer;
}

struct LoadBalancedBackend lb_get_backend(struct LoadBalancer *balancer,
                                          struct LoadBalancedFlow *flow,
                                          vigor_time_t now,
                                          uint16_t wan_device) {
  int flow_index;
  struct LoadBalancedBackend backend;
  if (map_get(balancer->state->flow_to_flow_id, flow, &flow_index) == 0) {
    int backend_index = 0;
    int found = cht_find_preferred_available_backend(
        (uint64_t)LoadBalancedFlow_hash(flow), balancer->state->cht,
        balancer->state->active_backends, balancer->state->cht_height,
        balancer->state->backend_capacity, &backend_index);
    if (found) {
      if (dchain_allocate_new_index(balancer->state->flow_chain, &flow_index,
                                    now) != 0) {
        struct LoadBalancedFlow *vec_flow;
        uint32_t *vec_flow_id_to_backend_id;
        vector_borrow(balancer->state->flow_heap, flow_index,
                      (void **)&vec_flow);
        memcpy(vec_flow, flow, sizeof(struct LoadBalancedFlow));
        vector_borrow(balancer->state->flow_id_to_backend_id, flow_index,
                      (void **)&vec_flow_id_to_backend_id);
        *vec_flow_id_to_backend_id = backend_index;
        vector_return(balancer->state->flow_id_to_backend_id, flow_index,
                      (void *)vec_flow_id_to_backend_id);
        map_put(balancer->state->flow_to_flow_id, vec_flow, flow_index);
        vector_return(balancer->state->flow_heap, flow_index,
                      vec_flow); // another half is in the map

      } // Doesn't matter if we can't insert
      struct LoadBalancedBackend *vec_backend;
      vector_borrow(balancer->state->backends, backend_index,
                    (void **)&vec_backend);
      memcpy(&backend, vec_backend, sizeof(struct LoadBalancedBackend));
      vector_return(balancer->state->backends, backend_index,
                    (void *)vec_backend);
    } else {
      // Drop
      backend.nic = wan_device; // The wan interface.
    }

  } else {
    uint32_t *vec_backend_index;
    vector_borrow(balancer->state->flow_id_to_backend_id, flow_index,
                  (void **)&vec_backend_index);
    uint32_t backend_index = *vec_backend_index;
    vector_return(balancer->state->flow_id_to_backend_id, flow_index,
                  (void *)vec_backend_index);
    if (0 == dchain_is_index_allocated(balancer->state->active_backends,
                                       backend_index)) {
      struct LoadBalancedFlow *flow_key;
      // Nevermind the flow_id_to_backend_id, its entry
      // is automatically invalidated, by erasing the map entry.
      vector_borrow(balancer->state->flow_heap, flow_index, (void **)&flow_key);
      // could use `flow_key` just as well here, but
      // current impl of symbex models does not support
      // connecting a map with its keystore.
      map_erase(balancer->state->flow_to_flow_id, flow, (void **)&flow_key);

      dchain_free_index(balancer->state->flow_chain, flow_index);
      vector_return(balancer->state->flow_heap, flow_index, (void *)flow_key);
      return lb_get_backend(balancer, flow, now, wan_device);
    } else {
      dchain_rejuvenate_index(balancer->state->flow_chain, flow_index, now);

      struct LoadBalancedBackend *vec_backend;
      vector_borrow(balancer->state->backends, backend_index,
                    (void **)&vec_backend);
      memcpy(&backend, vec_backend, sizeof(struct LoadBalancedBackend));
      vector_return(balancer->state->backends, backend_index,
                    (void *)vec_backend);
    }
  }

  return backend;
}

void lb_process_heartbit(struct LoadBalancer *balancer,
                         struct LoadBalancedFlow *flow,
                         struct rte_ether_addr mac_addr, int nic,
                         vigor_time_t now) {
  int backend_index;
  if (map_get(balancer->state->ip_to_backend_id, &flow->src_ip,
              &backend_index) == 0) {
    if (0 != dchain_allocate_new_index(balancer->state->active_backends,
                                       &backend_index, now)) {
      struct LoadBalancedBackend *new_backend;
      vector_borrow(balancer->state->backends, backend_index,
                    (void **)&new_backend);
      new_backend->ip = flow->src_ip;
      new_backend->mac = mac_addr;
      new_backend->nic = nic;

      vector_return(balancer->state->backends, backend_index,
                    (void *)new_backend);
      uint32_t *ip;
      vector_borrow(balancer->state->backend_ips, backend_index, (void **)&ip);
      *ip = flow->src_ip;
      map_put(balancer->state->ip_to_backend_id, ip, backend_index);
      vector_return(balancer->state->backend_ips, backend_index, (void *)ip);
    }
    // Otherwise ignore this backend, we are full.
  } else {
    // Removed assert, because it is not trivial to satisfy during symbex
    // assert(dchain_is_index_allocated(balancer->state->active_backends,
    // backend_index));
    dchain_rejuvenate_index(balancer->state->active_backends, backend_index,
                            now);
  }
}

void lb_expire_flows(struct LoadBalancer *balancer, vigor_time_t time) {
  assert(time >= 0); // we don't support the past
  assert(sizeof(vigor_time_t) <= sizeof(uint64_t));
  uint64_t time_u = (uint64_t)time; // OK because of the two asserts
  vigor_time_t last_time =
      time_u - balancer->flow_expiration_time * 1000; // us to ns
  expire_items_single_map(balancer->state->flow_chain,
                          balancer->state->flow_heap,
                          balancer->state->flow_to_flow_id, last_time);
}

void lb_expire_backends(struct LoadBalancer *balancer, vigor_time_t time) {
  assert(time >= 0); // we don't support the past
  assert(sizeof(vigor_time_t) <= sizeof(uint64_t));
  uint64_t time_u = (uint64_t)time; // OK because of the two asserts
  vigor_time_t last_time =
      time_u - balancer->backend_expiration_time * 1000; // us to ns
  expire_items_single_map(balancer->state->active_backends,
                          balancer->state->backend_ips,
                          balancer->state->ip_to_backend_id, last_time);
}
