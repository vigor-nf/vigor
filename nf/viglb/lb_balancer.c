#include "lb_balancer.h"

#include "lib/containers/map.h"
#include "lib/containers/vector.h"
#include "lib/containers/double-chain.h"
#include "lib/expirator.h"

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>


struct LoadBalancer {
	uint32_t flow_capacity;
	uint32_t expiration_time;
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
	int hash = 31;

	hash += flow->src_ip;
	hash *= 17;

	hash += flow->src_port;
	hash *= 17;

	hash += flow->dst_port;
	hash *= 17;

	hash += flow->protocol;
	hash *= 17;

	return hash;
}

void
lb_flow_init(void* obj) {
	// Nothing.
	(void) obj;
}


struct LoadBalancer*
lb_allocate_balancer(uint32_t flow_capacity, uint32_t expiration_time, uint16_t backend_count) {
	struct LoadBalancer* balancer = malloc(sizeof(struct LoadBalancer));
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
	balancer->expiration_time = expiration_time;

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
	int bucket_int;
	if (map_get(balancer->flow_buckets, flow, &bucket_int) == 0) {
		int hash = lb_flow_hash(flow);
		bucket_int = hash % balancer->backend_count;

		int index;
		if (map_size(balancer->flow_buckets) < balancer->flow_capacity &&
                    dchain_allocate_new_index(balancer->flow_indices, &index, now) != 0) {
			struct LoadBalancedFlow* own_flow;
			vector_borrow_full(balancer->flow_heap, index, (void**) &own_flow);

			memcpy(own_flow, flow, sizeof(struct LoadBalancedFlow));

			map_put(balancer->flow_buckets, own_flow, bucket_int);

			vector_return_full(balancer->flow_heap, index, own_flow);
		}
		// Doesn't matter if we can't insert
	}

	return (uint16_t) bucket_int;
}

void lb_expire_flows(struct LoadBalancer* balancer, time_t now) {
	time_t time = now - balancer->expiration_time;
	expire_items_single_map(balancer->flow_indices, balancer->flow_heap, balancer->flow_buckets, time);
}

#ifdef KLEE_VERIFICATION
struct Map** lb_get_buckets(struct LoadBalancer* balancer) {
	return balancer->vector_buckets;
}
struct Vector** lb_get_heap(struct LoadBalancer* balancer) {
	return balancer->vector_heap;
}
struct DoubleChain** lb_get_indices(struct LoadBalancer* balancer) {
	return balancer->vector_indices;
}
#endif
