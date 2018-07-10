#pragma once

#include "lib/nf_time.h"

#include <stdint.h>


struct LoadBalancedFlow {
	int32_t src_ip;
	int16_t src_port;
	int16_t dst_port;
	uint8_t protocol;
};

struct LoadBalancer;
struct LoadBalancer* lb_allocate_balancer(uint32_t flow_capacity, uint32_t expiration_time, uint16_t backend_count);
uint16_t lb_get_backend(struct LoadBalancer* balancer, struct LoadBalancedFlow* flow, time_t now);
void lb_expire_flows(struct LoadBalancer* balancer, time_t now);

#ifdef KLEE_VERIFICATION
struct Map** lb_get_buckets(struct LoadBalancer* balancer);
struct Vector** lb_get_heap(struct LoadBalancer* balancer);
struct DoubleChain** lb_get_indices(struct LoadBalancer* balancer);
#endif
