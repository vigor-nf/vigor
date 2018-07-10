#pragma once

#include "lib/nf_time.h"

struct LoadBalancedFlow {
	int32_t src_ip;
	int16_t src_port;
	int16_t dst_port;
	uint8_t protocol;
};

struct LoadBalancer;
struct LoadBalancer* lb_allocate_balancer(uint16_t backend_count, uint32_t expiration_time);
uint16_t lb_get_backend(struct LoadBalancer* balancer, struct LoadBalancedFlow* flow, time_t now);
void lb_expire_flows(struct LoadBalancer* balancer, time_t now);

#ifdef KLEE_VERIFICATION
struct DoubleChain** lb_get_dchain(struct LoadBalancer* balancer);
struct Map** lb_get_map(struct LoadBalancer* balancer);
#endif
