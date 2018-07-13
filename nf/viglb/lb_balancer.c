#include "lb_balancer.h"

#include "lib/containers/map.h"
#include "lib/containers/vector.h"
#include "lib/containers/double-chain.h"
#include "lib/expirator.h"

#include <assert.h>
#include <stdlib.h>
#include <string.h>


#ifdef KLEE_VERIFICATION
#include <klee/klee.h>

#include "lib/stubs/containers/map-stub-control.h"
#include "lib/stubs/containers/vector-stub-control.h"

#include "lib/stubs/containers/str-descr.h"

#define FIELD(struct_name, name, size) { offsetof(struct struct_name, name), sizeof(size), #name }
#define FFIELD(name, size) FIELD(LoadBalancedFlow, name, size)
#define BFIELD(name, size) FIELD(LoadBalancedBackend, name, size)

struct str_field_descr lb_flow_fields[] = {
	FFIELD(src_ip, uint32_t), FFIELD(src_port, uint16_t), FFIELD(dst_port, uint16_t), FFIELD(protocol, uint8_t)
};

struct str_field_descr lb_backend_fields[] = {
	BFIELD(index, uint16_t)
};

#undef BFIELD
#undef FFIELD
#undef FIELD

void lb_hack_concretize_backend(uint16_t backend_count, struct LoadBalancedBackend* backend) {
	klee_assume(backend->index >= 0);
	klee_assume(backend->index < backend_count);
	for(unsigned b = 0; b < backend_count; b++) if (backend->index == b) { backend->index = b; break; }
}
#endif


struct LoadBalancer {
	uint32_t flow_capacity;
	uint32_t flow_expiration_time;
	uint16_t backend_count;
	struct Map* flow_indices;
	struct Vector* flow_heap;
	struct Vector* flow_backends;
	struct DoubleChain* flow_chain;
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

void
lb_backend_init(void* obj) {
	// Nothing.
	(void) obj;
}


// We don't want the hash to show up in symbex, too complex to deal with
uint16_t
lb_compute_backend(struct LoadBalancedFlow* flow, uint16_t backend_count) {
#ifdef KLEE_VERIFICATION
	uint16_t backend;
	klee_make_symbolic(&backend, sizeof(uint16_t), "backend");
	return backend;
#else
	return lb_flow_hash(flow) % backend_count;
#endif
}



struct LoadBalancer*
lb_allocate_balancer(uint32_t flow_capacity, uint32_t flow_expiration_time, uint16_t backend_count) {
	struct LoadBalancer* balancer = calloc(1, sizeof(struct LoadBalancer));
	if (balancer == NULL) {
		goto err;
	}

	if (map_allocate(lb_flow_equality, lb_flow_hash, flow_capacity, &(balancer->flow_indices)) == 0) {
		goto err;
	}

	if (vector_allocate(sizeof(struct LoadBalancedFlow), flow_capacity, lb_flow_init, &(balancer->flow_heap)) == 0) {
		goto err;
	}

	if (vector_allocate(sizeof(struct LoadBalancedBackend), flow_capacity, lb_backend_init, &(balancer->flow_backends)) == 0) {
		goto err;
	}

	if (dchain_allocate(flow_capacity, &(balancer->flow_chain)) == 0) {
		goto err;
	}

	balancer->flow_capacity = flow_capacity;
	balancer->backend_count = backend_count;
	balancer->flow_expiration_time = flow_expiration_time;

#ifdef KLEE_VERIFICATION
	map_set_layout(balancer->flow_indices, lb_flow_fields, sizeof(lb_flow_fields)/sizeof(lb_flow_fields[0]), NULL, 0, "LoadBalancedFlow");
	vector_set_layout(balancer->flow_heap, lb_flow_fields, sizeof(lb_flow_fields)/sizeof(lb_flow_fields[0]), NULL, 0, "LoadBalancedFlow");
	vector_set_layout(balancer->flow_backends, lb_backend_fields, sizeof(lb_backend_fields)/sizeof(lb_backend_fields[0]), NULL, 0, "LoadBalancedBackend");
#endif

	return balancer;

err:
	if (balancer != NULL) {
		free(balancer->flow_indices);
		free(balancer->flow_heap);
		free(balancer->flow_backends);
		free(balancer->flow_chain);
	}

	free(balancer);

	return NULL;
}

struct LoadBalancedBackend
lb_get_backend(struct LoadBalancer* balancer, struct LoadBalancedFlow* flow, time_t now) {
	int index;
	struct LoadBalancedBackend backend;
	if (map_get(balancer->flow_indices, flow, &index) == 0) {
		backend.index = lb_compute_backend(flow, balancer->backend_count);

		if (map_size(balancer->flow_indices) < balancer->flow_capacity &&
                    dchain_allocate_new_index(balancer->flow_chain, &index, now) != 0) {
			struct LoadBalancedFlow* vec_flow;
			vector_borrow_full(balancer->flow_heap, index, (void**) &vec_flow);
			memcpy(vec_flow, flow, sizeof(struct LoadBalancedFlow));
			map_put(balancer->flow_indices, vec_flow, index);
			vector_return_half(balancer->flow_heap, index, vec_flow); // other half in map

			struct LoadBalancedBackend* vec_backend;
			vector_borrow_full(balancer->flow_backends, index, (void**) &vec_backend);
			memcpy(vec_backend, &backend, sizeof(struct LoadBalancedBackend));
			vector_return_full(balancer->flow_backends, index, vec_backend);

		}
		// Doesn't matter if we can't insert
	} else {
		struct LoadBalancedBackend* vec_backend;
		vector_borrow_full(balancer->flow_backends, index, (void**) &vec_backend);
		memcpy(&backend, vec_backend, sizeof(struct LoadBalancedBackend));
		vector_return_full(balancer->flow_backends, index, vec_backend);
	}

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

	expire_items_single_map(balancer->flow_chain, balancer->flow_heap, balancer->flow_indices, last_time);
}

#ifdef KLEE_VERIFICATION
struct Map** lb_get_indices(struct LoadBalancer* balancer) {
	return &(balancer->flow_indices);
}
struct Vector** lb_get_heap(struct LoadBalancer* balancer) {
	return &(balancer->flow_heap);
}
struct Vector** lb_get_backends(struct LoadBalancer* balancer) {
	return &(balancer->flow_backends);
}
struct DoubleChain** lb_get_chain(struct LoadBalancer* balancer) {
	return &(balancer->flow_chain);
}
#endif
