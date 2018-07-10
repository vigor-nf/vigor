#include "lb_balancer.h"

#include "lib/containers/map.h"
#include "lib/containers/vector.h"
#include "lib/containers/double-chain.h"
#include "lib/expirator.h"

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>


#ifdef KLEE_VERIFICATION
#include <klee/klee.h>

#include "lib/stubs/containers/map-stub-control.h"
#include "lib/stubs/containers/vector-stub-control.h"

#include "lib/stubs/containers/str-descr.h"

struct str_field_descr lb_flow_fields[] = {
  {offsetof(struct LoadBalancedFlow, src_ip), sizeof(uint32_t), "src_ip"},
  {offsetof(struct LoadBalancedFlow, src_port), sizeof(uint16_t), "src_port"},
  {offsetof(struct LoadBalancedFlow, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct LoadBalancedFlow, protocol), sizeof(uint8_t), "protocol"},
};

void lb_hack_concretize_backend(uint16_t backend_count, uint16_t* backend) {
	klee_assume(*backend >= 0);
	klee_assume(*backend < backend_count);
	for(unsigned b = 0; b < backend_count; b++) if (*backend == b) { *backend = b; break; }
}
#endif


struct LoadBalancer {
	uint32_t flow_capacity;
	uint32_t flow_expiration_time;
	uint16_t backend_count;
	struct Map* flow_buckets;
	struct Vector* flow_heap;
	struct DoubleChain* flow_indices;
};


bool
lb_flow_equality(void* objA, void* objB) {
	struct LoadBalancedFlow* flowA = objA;
	struct LoadBalancedFlow* flowB = objB;

	return flowA->src_ip == flowB->src_ip
	    && flowA->src_port == flowB->src_port
	    && flowA->dst_port == flowB->dst_port
	    && flowA->protocol == flowB->protocol;
}

int
lb_flow_hash(void* obj) {
	struct LoadBalancedFlow* flow = obj;
	uint64_t hash = 31;

	hash += flow->src_ip;
	hash *= 17;

	hash += flow->src_port;
	hash *= 17;

	hash += flow->dst_port;
	hash *= 17;

	hash += flow->protocol;
	hash *= 17;

	return (int) hash;
}

void
lb_flow_init(void* obj) {
	// Nothing.
	(void) obj;
}


struct LoadBalancer*
lb_allocate_balancer(uint32_t flow_capacity, uint32_t flow_expiration_time, uint16_t backend_count) {
	struct LoadBalancer* balancer = calloc(1, sizeof(struct LoadBalancer));
	if (balancer == NULL) {
		goto err;
	}

	if (map_allocate(lb_flow_equality, lb_flow_hash, flow_capacity, &(balancer->flow_buckets)) == 0) {
		goto err;
	}

	if (vector_allocate(sizeof(struct LoadBalancedFlow), flow_capacity, lb_flow_init, &(balancer->flow_heap)) == 0) {
		goto err;
	}

	if (dchain_allocate(flow_capacity, &(balancer->flow_indices)) == 0) {
		goto err;
	}

	balancer->flow_capacity = flow_capacity;
	balancer->backend_count = backend_count;
	balancer->flow_expiration_time = flow_expiration_time;

#ifdef KLEE_VERIFICATION
	map_set_layout(balancer->flow_buckets, lb_flow_fields, sizeof(lb_flow_fields)/sizeof(lb_flow_fields[0]), NULL, 0, "LoadBalancedFlow");
	vector_set_layout(balancer->flow_heap, lb_flow_fields, sizeof(lb_flow_fields)/sizeof(lb_flow_fields[0]), NULL, 0, "LoadBalancedFlow");
#endif

	return balancer;

err:
	if (balancer != NULL) {
		free(balancer->flow_buckets);
		free(balancer->flow_heap);
		free(balancer->flow_indices);
	}

	free(balancer);

	return NULL;
}

uint16_t lb_get_backend(struct LoadBalancer* balancer, struct LoadBalancedFlow* flow, time_t now) {
	int bucket;
	if (map_get(balancer->flow_buckets, flow, &bucket) == 0) {
		int hash = lb_flow_hash(flow);
		bucket = hash % balancer->backend_count;

		int index;
		if (map_size(balancer->flow_buckets) < balancer->flow_capacity &&
                    dchain_allocate_new_index(balancer->flow_indices, &index, now) != 0) {
			struct LoadBalancedFlow* own_flow;
			vector_borrow_full(balancer->flow_heap, index, (void**) &own_flow);

			memcpy(own_flow, flow, sizeof(struct LoadBalancedFlow));

			map_put(balancer->flow_buckets, own_flow, bucket);

			vector_return_full(balancer->flow_heap, index, own_flow);
		}
		// Doesn't matter if we can't insert
	}

	uint16_t backend = (uint16_t) bucket;

#ifdef KLEE_VERIFICATION
	lb_hack_concretize_backend(balancer->backend_count, &backend);
#endif

	return backend;
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

	expire_items_single_map(balancer->flow_indices, balancer->flow_heap, balancer->flow_buckets, last_time);
}

#ifdef KLEE_VERIFICATION
struct Map** lb_get_buckets(struct LoadBalancer* balancer) {
	return &(balancer->flow_buckets);
}
struct Vector** lb_get_heap(struct LoadBalancer* balancer) {
	return &(balancer->flow_heap);
}
struct DoubleChain** lb_get_indices(struct LoadBalancer* balancer) {
	return &(balancer->flow_indices);
}
#endif
