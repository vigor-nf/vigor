#include "lb_balancer.h"

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

// KLEE doesn't tolerate && in a klee_assume (see klee/klee#809),
// so we replace them with & during symbex but interpret them as && in the validator
#ifdef KLEE_VERIFICATION
#  define AND &
#else // KLEE_VERIFICATION
#  define AND &&
#endif // KLEE_VERIFICATION


struct LoadBalancer {
  uint32_t flow_capacity;
  uint32_t flow_expiration_time;
  struct Map* flow_to_flow_id;
  struct Vector* flow_heap;
  struct DoubleChain* flow_chain;

  struct Vector* flow_id_to_backend_id;

  uint32_t cht_height;
  uint32_t backend_expiration_time;
  uint32_t backend_capacity;
  struct Vector* backend_ips;
  struct Vector* backends;
  struct Map* ip_to_backend_id;
  struct DoubleChain* active_backends;
  struct Vector* cht;
};


#ifdef KLEE_VERIFICATION
#include <klee/klee.h>

#include <rte_ethdev.h>

#include "lib/stubs/containers/map-stub-control.h"
#include "lib/stubs/containers/vector-stub-control.h"

#include "lib/stubs/containers/str-descr.h"

extern struct LoadBalancer* balancer;

bool
lb_backend_id_condition(void* key, int value) {
  return 0 <= value AND value < balancer->backend_capacity;
}

bool
lb_flow_id_condition(void* key, int value) {
  return 0 <= value AND value < balancer->flow_capacity;
}

bool
lb_backend_condition(void* key, int index, void* state) {
  return 0 < ((struct LoadBalancedBackend*) key)->nic AND
         ((struct LoadBalancedBackend*) key)->nic < rte_eth_dev_count();
}

bool
lb_flow_id2backend_id_cond(void* key, int index, void* state) {
  return *(uint32_t*)key < balancer->backend_capacity;
}

struct str_field_descr uint32_field = {0, sizeof(uint32_t), "value"};
#endif//KLEE_VERIFICATION

void null_init(void* obj) {
  *(uint32_t*)obj = 0;
}

struct LoadBalancer*
lb_allocate_balancer(uint32_t flow_capacity, uint32_t backend_capacity,
                     uint32_t cht_height, uint32_t backend_expiration_time,
                     uint32_t flow_expiration_time) {
  struct LoadBalancer* balancer = calloc(1, sizeof(struct LoadBalancer));
  if (balancer == NULL) {
    goto err;
  }


  if (map_allocate(lb_flow_equality, lb_flow_hash, flow_capacity, &(balancer->flow_to_flow_id)) == 0) {
    goto err;
  }

  if (vector_allocate(sizeof(struct LoadBalancedFlow), flow_capacity, lb_flow_init, &(balancer->flow_heap)) == 0) {
    goto err;
  }

  if (vector_allocate(sizeof(uint32_t), flow_capacity, null_init, &(balancer->flow_id_to_backend_id)) == 0) {
    goto err;
  }

  if (dchain_allocate(flow_capacity, &(balancer->flow_chain)) == 0) {
    goto err;
  }

  if (vector_allocate(sizeof(uint32_t), backend_capacity, null_init, &(balancer->backend_ips)) == 0) {
    goto err;
  }

  if (vector_allocate(sizeof(struct LoadBalancedBackend), backend_capacity, lb_backend_init, &(balancer->backends)) == 0) {
    goto err;
  }

  if (map_allocate(lb_ip_equality, lb_ip_hash, backend_capacity, &(balancer->ip_to_backend_id)) == 0) {
    goto err;
  }

  if (dchain_allocate(backend_capacity, &(balancer->active_backends)) == 0) {
    goto err;
  }

  if (vector_allocate(sizeof(uint32_t), cht_height*backend_capacity, null_init, &(balancer->cht)) == 0) {
    goto err;
  }

#ifdef KLEE_VERIFICATION
  map_set_layout(balancer->flow_to_flow_id, lb_flow_fields, lb_flow_fields_number(), NULL, 0, "LoadBalancedFlow");
  map_set_entry_condition(balancer->flow_to_flow_id, lb_flow_id_condition);
  vector_set_layout(balancer->flow_heap, lb_flow_fields, lb_flow_fields_number(), NULL, 0, "LoadBalancedFlow");
  //vector_set_layout(balancer->flow_id_to_backend_id, &uint32_field, 1, NULL, 0, "uint32_t");
  vector_set_layout(balancer->flow_id_to_backend_id, NULL, 0, NULL, 0, "uint32_t");
  vector_set_entry_condition(balancer->flow_id_to_backend_id, lb_flow_id2backend_id_cond, balancer);
  //vector_set_layout(balancer->backend_ips, &uint32_field, 1, NULL, 0, "uint32_t");
  vector_set_layout(balancer->backend_ips, NULL, 0, NULL, 0, "uint32_t");
  vector_set_layout(balancer->backends,
                    lb_backend_fields, lb_backend_fields_number(),
                    lb_backend_nested_fields, lb_backend_nested_fields_number(),
                    "LoadBalancedBackend");
  vector_set_entry_condition(balancer->backends, lb_backend_condition, balancer);
  map_set_layout(balancer->ip_to_backend_id, &uint32_field, 1, NULL, 0, "uint32_t");
  map_set_entry_condition(balancer->ip_to_backend_id, lb_backend_id_condition);
  vector_set_layout(balancer->cht, NULL, 0, NULL, 0, "uint32_t");
#endif//KLEE_VERIFICATION

  cht_fill_cht(balancer->cht, cht_height, backend_capacity);

  balancer->flow_capacity = flow_capacity;
  balancer->backend_capacity = backend_capacity;
  balancer->flow_expiration_time = flow_expiration_time;
  balancer->cht_height = cht_height;
  balancer->backend_expiration_time = backend_expiration_time;

  return balancer;

err:
  if (balancer != NULL) {
    free(balancer->flow_to_flow_id);
    free(balancer->flow_heap);
    free(balancer->flow_chain);

    free(balancer->flow_id_to_backend_id);
    free(balancer->backend_ips);
    free(balancer->backends);
    free(balancer->ip_to_backend_id);
    free(balancer->active_backends);
    free(balancer->cht);
  }

  free(balancer);

  return NULL;
}

struct LoadBalancedBackend
lb_get_backend(struct LoadBalancer* balancer, struct LoadBalancedFlow* flow, time_t now) {
  int flow_index;
  struct LoadBalancedBackend backend;
  if (map_get(balancer->flow_to_flow_id, flow, &flow_index) == 0) {
    int backend_index = 0;
    int found =
      cht_find_preferred_available_backend((uint64_t) lb_flow_hash(flow),
                                           balancer->cht,
                                           balancer->active_backends,
                                           balancer->cht_height,
                                           balancer->backend_capacity,
                                           &backend_index);
    if (found) {
      if (dchain_allocate_new_index(balancer->flow_chain, &flow_index, now) != 0) {
        struct LoadBalancedFlow* vec_flow;
        uint32_t* vec_flow_id_to_backend_id;
        vector_borrow(balancer->flow_heap, flow_index, (void**)&vec_flow);
        memcpy(vec_flow, flow, sizeof(struct LoadBalancedFlow));
        vector_borrow(balancer->flow_id_to_backend_id, flow_index, (void**)&vec_flow_id_to_backend_id);
        *vec_flow_id_to_backend_id = backend_index;
        vector_return(balancer->flow_id_to_backend_id, flow_index, (void*)vec_flow_id_to_backend_id);
        map_put(balancer->flow_to_flow_id, vec_flow, flow_index);
        vector_return(balancer->flow_heap, flow_index, vec_flow); // other half in map

      }      // Doesn't matter if we can't insert
      struct LoadBalancedBackend* vec_backend;
      vector_borrow(balancer->backends, backend_index, (void**)&vec_backend);
      memcpy(&backend, vec_backend, sizeof(struct LoadBalancedBackend));
      vector_return(balancer->backends, backend_index, (void*)vec_backend);
      //klee_assert(backend.nic < rte_eth_dev_count());
    } else {
      //printf("dropping\n");
      // Drop
      backend.nic = 0;// The wan interface.
    }
    //klee_assert(backend.nic < rte_eth_dev_count());

  } else {
    uint32_t* vec_backend_index;
    vector_borrow(balancer->flow_id_to_backend_id, flow_index, (void**)&vec_backend_index);
    uint32_t backend_index = *vec_backend_index;
    vector_return(balancer->flow_id_to_backend_id, flow_index, (void*)vec_backend_index);
    if (0 == dchain_is_index_allocated(balancer->active_backends, backend_index)) {
      struct LoadBalancedFlow* flow_key;
      //Nevermind the flow_id_to_backend_id, its entry
      // is automatically invalidated, by erasing the map entry.
      vector_borrow(balancer->flow_heap, flow_index, (void**)&flow_key);
      // could use `flow_key` just as well here, but
      // current impl of symbex models does not support
      // connecting a map with its keystore.
      map_erase(balancer->flow_to_flow_id, flow, (void**)&flow_key);
      dchain_free_index(balancer->flow_chain, flow_index);
      vector_return(balancer->flow_heap, flow_index, (void*)flow_key);
      return lb_get_backend(balancer, flow, now);
    } else {
      dchain_rejuvenate_index(balancer->flow_chain, flow_index, now);

      struct LoadBalancedBackend* vec_backend;
      vector_borrow(balancer->backends, backend_index, (void**)&vec_backend);
      memcpy(&backend, vec_backend, sizeof(struct LoadBalancedBackend));
      vector_return(balancer->backends, backend_index, (void*)vec_backend);
    }
  }

#ifdef KLEE_VERIFICATION
  // Concretize the backend, to avoid propagating a symbolic device
  klee_assert(backend.nic < rte_eth_dev_count());
  for(uint16_t n = 0; n < rte_eth_dev_count(); n++) if (backend.nic == n) { backend.nic = n; break; }
#endif//KLEE_VERIFICATION

  return backend;
}

void lb_process_heartbit(struct LoadBalancer* balancer,
                         struct LoadBalancedFlow* flow,
                         struct ether_addr mac_addr,
                         int nic,
                         time_t now) {
  int backend_index;
  if (map_get(balancer->ip_to_backend_id, &flow->src_ip, &backend_index) == 0) {
    if (0 != dchain_allocate_new_index(balancer->active_backends,
                                       &backend_index, now)) {
      struct LoadBalancedBackend* new_backend;
      vector_borrow(balancer->backends, backend_index, (void**)&new_backend);
      new_backend->ip = flow->src_ip;
      new_backend->mac = mac_addr;
      new_backend->nic = nic;

      vector_return(balancer->backends, backend_index, (void*)new_backend);
      uint32_t* ip;
      vector_borrow(balancer->backend_ips, backend_index, (void**)&ip);
      *ip = flow->src_ip;
      map_put(balancer->ip_to_backend_id, ip, backend_index);
      vector_return(balancer->backend_ips, backend_index, (void*)ip);
    }
    //Otherwise ignore this backend, we are full.
  } else {
    // Removed assert, because it is not trivial to satisfy during symbex
    //assert(dchain_is_index_allocated(balancer->active_backends, backend_index));
    dchain_rejuvenate_index(balancer->active_backends, backend_index, now);
  }
}

void lb_expire_flows(struct LoadBalancer* balancer, time_t now) {
  if (now < balancer->flow_expiration_time) return;

  // This is hacky - we want to make sure the sanitization doesn't
  // extend our time_t value in 128 bits, which would confuse the validator.
  // So we "prove" by hand that it's OK...
  assert(sizeof(uint64_t) == sizeof(time_t));
  if (now < 0) return; // we don't support the past
  uint64_t now_u = (uint64_t) now; // OK since assert above passed and now > 0
  uint64_t last_time_u = now_u - balancer->flow_expiration_time; // OK because now >= flow_expiration_time >= 0
  time_t last_time = (time_t) last_time_u; // OK since the assert above passed

  expire_items_single_map(balancer->flow_chain, balancer->flow_heap, balancer->flow_to_flow_id, last_time);
}

void lb_expire_backends(struct LoadBalancer* balancer, time_t now) {
  if (now < balancer->backend_expiration_time) return;

  // This is hacky - we want to make sure the sanitization doesn't
  // extend our time_t value in 128 bits, which would confuse the validator.
  // So we "prove" by hand that it's OK...
  assert(sizeof(uint64_t) == sizeof(time_t));
  if (now < 0) return; // we don't support the past
  uint64_t now_u = (uint64_t) now; // OK since assert above passed and now > 0
  uint64_t last_time_u = now_u - balancer->backend_expiration_time; // OK because now >= flow_expiration_time >= 0
  time_t last_time = (time_t) last_time_u; // OK since the assert above passed

  expire_items_single_map(balancer->active_backends, balancer->backend_ips, balancer->ip_to_backend_id, last_time);
}

#ifdef KLEE_VERIFICATION

  struct Map** lb_get_flow_to_flow_id(struct LoadBalancer* balancer) { return &(balancer->flow_to_flow_id); }
  struct Vector** lb_get_flow_heap(struct LoadBalancer* balancer) { return &(balancer->flow_heap); }
  struct DoubleChain** lb_get_flow_chain(struct LoadBalancer* balancer) { return &(balancer->flow_chain); }
  struct Vector** lb_get_flow_id_to_backend_id(struct LoadBalancer* balancer) { return &(balancer->flow_id_to_backend_id); }
  struct Vector** lb_get_backend_ips(struct LoadBalancer* balancer) { return &(balancer->backend_ips); }
  struct Vector** lb_get_backends(struct LoadBalancer* balancer) { return &(balancer->backends); }
  struct Map** lb_get_ip_to_backend_id(struct LoadBalancer* balancer) { return &(balancer->ip_to_backend_id); }
  struct DoubleChain** lb_get_active_backends(struct LoadBalancer* balancer) { return &(balancer->active_backends); }
  struct Vector** lb_get_cht(struct LoadBalancer* balancer) { return &(balancer->cht); }
#endif//KLEE_VERIFICATION
