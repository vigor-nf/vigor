#ifndef _LB_BALANCER_H_INCLUDED_ // cannot use pragma once, included by VeriFast
#define _LB_BALANCER_H_INCLUDED_


#include "lib/stubs/mbuf_content.h"
#include "lib/containers/vector.h"
#include "lib/containers/double-chain.h"
#include "lib/containers/cht.h"

#include "lb_flow.h.gen.h"
#include "lb_backend.h.gen.h"
#include "ip_addr.h.gen.h"


struct LoadBalancer;
struct LoadBalancer* lb_allocate_balancer(uint32_t flow_capacity,
                                          uint32_t backend_capacity,
                                          uint32_t cht_height,
                                          uint32_t backend_expiration_time,
                                          uint32_t flow_expiration_time);
struct LoadBalancedBackend lb_get_backend(struct LoadBalancer* balancer, struct LoadBalancedFlow* flow, vigor_time_t now);
void lb_expire_flows(struct LoadBalancer* balancer, vigor_time_t now);
void lb_expire_backends(struct LoadBalancer* balancer, vigor_time_t now);
void lb_process_heartbit(struct LoadBalancer* balancer,
                         struct LoadBalancedFlow* flow,
                         struct ether_addr mac_addr,
                         int nic,
                         vigor_time_t now);

#endif // _LB_BALANCER_H_INCLUDED_
