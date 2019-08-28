#include "fw_flowmanager.h"

#include <assert.h>
#include <stdlib.h>
#include <string.h> //for memcpy
#include <rte_ethdev.h>

#include "libvig/verified/double-chain.h"
#include "libvig/verified/map.h"
#include "libvig/verified/vector.h"
#include "libvig/verified/expirator.h"

#include "state.h"

struct FlowManager {
  struct State *state;
  vigor_time_t expiration_time; /*seconds*/
};

struct FlowManager *flow_manager_allocate(uint16_t fw_device,
                                          vigor_time_t expiration_time,
                                          uint64_t max_flows) {
  struct FlowManager *manager =
      (struct FlowManager *)malloc(sizeof(struct FlowManager));
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

void flow_manager_allocate_or_refresh_flow(struct FlowManager *manager,
                                           struct FlowId *id,
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

  struct FlowId *key = 0;
  vector_borrow(manager->state->fv, index, (void **)&key);
  memcpy((void *)key, (void *)id, sizeof(struct FlowId));
  map_put(manager->state->fm, key, index);
  vector_return(manager->state->fv, index, key);
  uint32_t *int_dev;
  vector_borrow(manager->state->int_devices, index, (void **)&int_dev);
  *int_dev = internal_device;
  vector_return(manager->state->int_devices, index, int_dev);
}

void flow_manager_expire(struct FlowManager *manager, vigor_time_t time) {
  assert(time >= 0); // we don't support the past
  assert(sizeof(vigor_time_t) <= sizeof(uint64_t));
  uint64_t time_u = (uint64_t)time; // OK because of the two asserts
  vigor_time_t last_time = time_u - manager->expiration_time * 1000; // us to ns
  expire_items_single_map(manager->state->heap, manager->state->fv,
                          manager->state->fm, last_time);
}

bool flow_manager_get_refresh_flow(struct FlowManager *manager,
                                   struct FlowId *id, vigor_time_t time,
                                   uint32_t *internal_device) {
  int index;
  if (map_get(manager->state->fm, id, &index) == 0) {
    return false;
  }
  uint32_t *int_dev;
  vector_borrow(manager->state->int_devices, index, (void **)&int_dev);
  *internal_device = *int_dev;
  vector_return(manager->state->int_devices, index, int_dev);
  dchain_rejuvenate_index(manager->state->heap, index, time);
  return true;
}
