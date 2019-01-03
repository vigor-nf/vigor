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
	//struct DoubleMap* table;
  struct Map* in_table;
  struct Vector* in_keys;
  struct Vector* in_values;
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
flow_manager_get_in_keys(struct FlowManager* manager) {
	return &(manager->in_keys);
}

struct Vector**
flow_manager_get_in_values(struct FlowManager* manager) {
	return &(manager->in_values);
}

bool
flow_consistency(void* value, int index, void* state) {
	//struct FlowId* int_id = key_a;
	//struct FlowId* ext_id = key_b;
	struct Flow* flow = value;
	struct FlowManager* manager = state;
	return ( 0 <= flow->internal_device ) & ( flow->internal_device < rte_eth_dev_count() ) &
		( flow->internal_device != manager->nat_device ) &
		/* ( flow->external_id.src_port == flow->internal_id.dst_port ) & */
		/* ( flow->external_id.src_ip == flow->internal_id.dst_ip ) & */
		/* ( flow->external_id.protocol == flow->internal_id.protocol ) & */
		( flow->external_id.dst_port == manager->starting_port + index );
}

void
concretize_devices(struct FlowManager* manager, struct Flow* f) {
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

	/* if (dmap_allocate(flow_id_eq, flow_id_hash, flow_id_eq, flow_id_hash, */
	/* 		  sizeof(struct Flow), flow_copy, flow_destroy, flow_extract_keys, flow_pack_keys, */
	/* 		  max_flows, max_flows, */
	/* 		  &(manager->table)) == 0) { */
	/* 	free(manager); */
	/* 	return NULL; */
	/* } */
  if (map_allocate(flow_id_eq, flow_id_hash, max_flows, &(manager->in_table)) == 0) {
    // Do not free stuff, as we are exiting anyway
    return NULL;
  }

  if (vector_allocate(sizeof(struct FlowId), max_flows, flow_id_allocate, &(manager->in_keys)) == 0) {
    // Do not free stuff, as we are exiting anyway
    return NULL;
  }

  if (vector_allocate(sizeof(struct Flow), max_flows, flow_allocate, &(manager->in_values)) == 0) {
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
  map_set_layout(manager->in_table, flow_id_descrs, sizeof(flow_id_descrs)/sizeof(flow_id_descrs[0]),
                 NULL, 0, "FlowId");
  vector_set_layout(manager->in_keys, flow_id_descrs, sizeof(flow_id_descrs)/sizeof(flow_id_descrs[0]),
                    NULL, 0, "FlowId");
  vector_set_layout(manager->in_values, flow_descrs, sizeof(flow_descrs)/sizeof(flow_descrs[0]),
                    flow_nests, sizeof(flow_nests)/sizeof(flow_nests[0]), "Flow");
  vector_set_entry_condition(manager->in_values, flow_consistency, manager);
	/* dmap_set_layout(manager->table, */
	/* 		flow_id_descrs, sizeof(flow_id_descrs)/sizeof(struct str_field_descr), */
	/* 		flow_id_descrs, sizeof(flow_id_descrs)/sizeof(struct str_field_descr), */
	/* 		flow_descrs, sizeof(flow_descrs)/sizeof(struct str_field_descr), */
	/* 		flow_nests, sizeof(flow_nests)/sizeof(struct nested_field_descr)); */
	/* dmap_set_entry_condition(manager->table, flow_consistency, manager); */
#endif

	return manager;
}

bool
flow_manager_allocate_flow(struct FlowManager* manager, struct FlowId* id, uint16_t internal_device, time_t time, struct Flow* out_flow) {
	int index;
	if (dchain_allocate_new_index(manager->chain, &index, time) == 0) {
		return false;
	}

	uint16_t port = manager->starting_port + index;
	struct Flow flow = {
		.internal_id = *id,
		.external_id = {
			.src_port = id->dst_port,
			.dst_port = port,
			.src_ip = id->dst_ip,
			.dst_ip = manager->nat_ip,
			.protocol = id->protocol
		},
		.internal_device = internal_device
	};

  struct FlowId* key = 0;
  struct Flow* value = 0;
  vector_borrow(manager->in_keys, index, (void**)&key);
  vector_borrow(manager->in_values, index, (void**)&value);
  memcpy((void*)key, (void*)id, sizeof(struct FlowId));
  memcpy((void*)value, (void*)&flow, sizeof(struct Flow));
  map_put(manager->in_table, key, index);

  //This can be optimized out, if we use "out_flow" rightaway, without going through "flow"
  memcpy((void*)out_flow, (void*)value, sizeof(struct Flow));

  vector_return(manager->in_keys, index, key);
  vector_return(manager->in_values, index, value);
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

	expire_items_single_map(manager->chain, manager->in_keys, manager->in_table, last_time);
}


static void
flow_manager_get_and_rejuvenate(struct FlowManager* manager, int index, time_t time, struct Flow* out_flow) {
  struct Flow* value;
  vector_borrow(manager->in_values, index, (void**)&value);
  memcpy((void*)out_flow, (void*)value, sizeof(struct Flow));
  vector_return(manager->in_values, index, value);
	dchain_rejuvenate_index(manager->chain, index, time);

#ifdef KLEE_VERIFICATION
	concretize_devices(manager, out_flow);
#endif
}

bool
flow_manager_get_internal(struct FlowManager* manager, struct FlowId* id, time_t time, struct Flow* out_flow) {
	int index;
	if (map_get(manager->in_table, id, &index) == 0) {
		return false;
	}

	flow_manager_get_and_rejuvenate(manager, index, time, out_flow);
	return true;
}

bool
flow_manager_get_external(struct FlowManager* manager, struct FlowId* id, time_t time, struct Flow* out_flow) {
	int index = id->dst_port - manager->starting_port;
  if (dchain_is_index_allocated(manager->chain, index) == 0) {
    return false;
  }

	flow_manager_get_and_rejuvenate(manager, index, time, out_flow);
	return true;
}
