#include "nat_flowmanager.h"

#include <assert.h>
#include <stdlib.h>
#include <string.h>//for memcpy

#include "lib/containers/double-chain.h"
#include "lib/containers/map.h"
#include "lib/containers/vector.h"
#include "lib/expirator.h"

struct FlowManager {
	uint16_t starting_port;
	uint32_t nat_ip;
	uint16_t nat_device;
	uint32_t expiration_time; /*seconds*/
	struct DoubleChain* chain;
  struct Map* in_table;
  struct Vector* in_vec;
};

#ifdef KLEE_VERIFICATION
#include <rte_ethdev.h>
#include "lib/stubs/containers/map-stub-control.h" //<- for set layout
#include "lib/stubs/containers/vector-stub-control.h" //<- for set entry cond

struct DoubleChain**
flow_manager_get_chain(struct FlowManager* manager) {
	return &(manager->chain);
}

struct Map**
flow_manager_get_in_table(struct FlowManager* manager) {
	return &(manager->in_table);
}

struct Vector**
flow_manager_get_in_vec(struct FlowManager* manager) {
	return &(manager->in_vec);
}

bool
flow_consistency(void* value, int index, void* state) {
	struct FlowId* flow_id = value;
	struct FlowManager* manager = state;
	return ( 0 <= flow_id->internal_device ) & ( flow_id->internal_device < rte_eth_dev_count() ) &
		( flow_id->internal_device != manager->nat_device );
}

void
concretize_devices(struct FlowManager* manager, struct FlowId* f) {
	int count = rte_eth_dev_count();

	klee_assume(f->internal_device >= 0);
	klee_assume(f->internal_device < count);

	for(unsigned d = 0; d < count; d++) if (f->internal_device == d) { f->internal_device = d; break; }
}
#endif//KLEE_VERIFICATION

struct FlowManager*
flow_manager_allocate(uint16_t starting_port,
                      uint32_t nat_ip,
                      uint16_t nat_device,
                      uint32_t expiration_time,
                      uint64_t max_flows) {
	struct FlowManager* manager = (struct FlowManager*) malloc(sizeof(struct FlowManager));
	if (manager == NULL) {
		return NULL;
	}

	manager->starting_port = starting_port;
	manager->nat_ip = nat_ip;
	manager->nat_device = nat_device;
	manager->expiration_time = expiration_time;

  manager->in_table = NULL;
  manager->in_vec = NULL;
  manager->chain = NULL;

  if (map_allocate(FlowId_eq, FlowId_hash, max_flows, &(manager->in_table)) == 0) {
    // Do not free stuff, as we are exiting anyway
    return NULL;
  }

  if (vector_allocate(sizeof(struct FlowId), max_flows, FlowId_allocate, &(manager->in_vec)) == 0) {
    // Do not free stuff, as we are exiting anyway
    return NULL;
  }

	if (dchain_allocate(max_flows, &(manager->chain)) == 0) {
    // Do not free stuff, as we are exiting anyway
		return NULL;
	}

#ifdef KLEE_VERIFICATION
  //NOTE: need more entry conditions? e.g. to ensure that the in_table value indexes
  // fit into the in_values vector, or that flow_ids feature a proper internal port.
  map_set_layout(manager->in_table, FlowId_descrs, sizeof(FlowId_descrs)/sizeof(FlowId_descrs[0]),
                 NULL, 0, "FlowId");
  vector_set_layout(manager->in_vec, FlowId_descrs, sizeof(FlowId_descrs)/sizeof(FlowId_descrs[0]),
                    NULL, 0, "FlowId");
  vector_set_entry_condition(manager->in_vec, flow_consistency, manager);
#endif

	return manager;
}

bool
flow_manager_allocate_flow(struct FlowManager* manager, struct FlowId* id,
                           uint16_t internal_device, time_t time,
                           uint16_t* external_port) {
	int index;
	if (dchain_allocate_new_index(manager->chain, &index, time) == 0) {
		return false;
	}

  *external_port = manager->starting_port + index;

  struct FlowId* key = 0;
  vector_borrow(manager->in_vec, index, (void**)&key);
  memcpy((void*)key, (void*)id, sizeof(struct FlowId));
  map_put(manager->in_table, key, index);
  vector_return(manager->in_vec, index, key);
	return true;
}

void
flow_manager_expire(struct FlowManager* manager, time_t time) {
	// too early, nothing can expire yet.
	if (time < manager->expiration_time) {
		return;
	}

	// This is convoluted - we want to make sure the sanitization doesn't
	// extend our time_t value in 128 bits, which would confuse the validator.
	// So we "prove" by hand that it's OK...
	if (time < 0) return; // we don't support the past
	assert(sizeof(time_t) <= sizeof(uint64_t));
	uint64_t time_u = (uint64_t) time; // OK since assert above passed and time > 0
	uint64_t last_time_u = time_u - manager->expiration_time; // OK because time >= expiration_time >= 0
	assert(sizeof(uint64_t) <= sizeof(time_t));
	time_t last_time = (time_t) last_time_u; // OK since the assert above passed

	expire_items_single_map(manager->chain, manager->in_vec, manager->in_table, last_time);
}


bool
flow_manager_get_internal(struct FlowManager* manager, struct FlowId* id,
                          time_t time,
                          uint16_t* external_port) {
	int index;
	if (map_get(manager->in_table, id, &index) == 0) {
		return false;
	}
  *external_port = index + manager->starting_port;
	dchain_rejuvenate_index(manager->chain, index, time);
  return true;
}

bool
flow_manager_get_external(struct FlowManager* manager, uint16_t external_port,
                          time_t time,
                          struct FlowId* out_flow) {
	int index = external_port - manager->starting_port;
  if (dchain_is_index_allocated(manager->chain, index) == 0) {
    return false;
  }

  struct FlowId* key = 0;
  vector_borrow(manager->in_vec, index, (void**)&key);
  memcpy((void*)out_flow, (void*)key, sizeof(struct FlowId));
  vector_return(manager->in_vec, index, key);

	dchain_rejuvenate_index(manager->chain, index, time);

#ifdef KLEE_VERIFICATION
	concretize_devices(manager, out_flow);
#endif
	return true;
}
