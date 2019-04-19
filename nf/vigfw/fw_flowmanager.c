#include "fw_flowmanager.h"

#include <assert.h>
#include <stdlib.h>
#include <string.h>//for memcpy
#include <rte_ethdev.h>

#include "lib/containers/double-chain.h"
#include "lib/containers/map.h"
#include "lib/containers/vector.h"
#include "lib/expirator.h"

#include "fw_state.h"

struct FlowManager {
  struct State* state;
  uint64_t expiration_time; /*seconds*/
};

bool
int_dev_bounds(void* value, int index, void* state) {
  uint32_t* int_dev = value;
  struct State* st = state;
  return ( *int_dev < rte_eth_dev_count() ) AND
         ( *int_dev != st->fw_device );
}

struct FlowManager*
flow_manager_allocate(uint16_t fw_device,
                      uint64_t expiration_time,
                      uint64_t max_flows) {
  struct FlowManager* manager = (struct FlowManager*) malloc(sizeof(struct FlowManager));
  if (manager == NULL) {
    return NULL;
  }
  manager->state = alloc_state(max_flows, fw_device);
  if (manager->state == NULL) {
    return NULL;
  }

  manager->expiration_time = expiration_time;

  return manager;
}

void
flow_manager_allocate_or_refresh_flow(struct FlowManager* manager,
                                      struct FlowId* id,
                                      uint32_t internal_device,
                                      vigor_time_t time) {
  int index;
  if (map_get(manager->state->fm, id, &index)) {
    dchain_rejuvenate_index(manager->state->heap, index, time);
    return;
  }
  if (!dchain_allocate_new_index(manager->state->heap, &index, time)) {
    // No luck, the flow table is full, but we can at least let the
    // outgoing traffic out.
    return;
  }

  struct FlowId* key = 0;
  vector_borrow(manager->state->fv, index, (void**)&key);
  memcpy((void*)key, (void*)id, sizeof(struct FlowId));
  map_put(manager->state->fm, key, index);
  vector_return(manager->state->fv, index, key);
  uint32_t *int_dev;
  vector_borrow(manager->state->int_devices, index, (void**)&int_dev);
  *int_dev = internal_device;
  vector_return(manager->state->int_devices, index, int_dev);
}

void
flow_manager_expire(struct FlowManager* manager, vigor_time_t time) {
  // too early, nothing can expire yet.
  if (time < manager->expiration_time) {
    return;
  }

  // This is convoluted - we want to make sure the sanitization doesn't
  // extend our vigor_time_t value in 128 bits, which would confuse the validator.
  // So we "prove" by hand that it's OK...
  if (time < 0) return; // we don't support the past
  assert(sizeof(vigor_time_t) <= sizeof(int64_t));
  uint64_t time_u = (uint64_t) time; // OK since assert above passed and time > 0
  uint64_t last_time_u = time_u - manager->expiration_time; // OK because time >= expiration_time >= 0
  assert(sizeof(int64_t) <= sizeof(vigor_time_t));
  vigor_time_t last_time = (vigor_time_t) last_time_u; // OK since the assert above passed

  expire_items_single_map(manager->state->heap, manager->state->fv, manager->state->fm, last_time);
}

bool
flow_manager_get_refresh_flow(struct FlowManager* manager,
                              struct FlowId* id,
                              vigor_time_t time,
                              uint32_t* internal_device) {
  int index;
  if (map_get(manager->state->fm, id, &index) == 0) {
    return false;
  }
  uint32_t *int_dev;
  vector_borrow(manager->state->int_devices, index, (void**)&int_dev);
  *internal_device = *int_dev;
  vector_return(manager->state->int_devices, index, int_dev);
  dchain_rejuvenate_index(manager->state->heap, index, time);
  return true;
}
