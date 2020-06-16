#ifndef _LB_BALANCER_H_INCLUDED_ // cannot use pragma once, included by VeriFast
#define _LB_BALANCER_H_INCLUDED_

#include "libvig/verified/vector.h"
#include "libvig/verified/double-chain.h"
#include "libvig/verified/cht.h"

#include <rte_ether.h>

#include "lb_flow.h.gen.h"
#include "lb_backend.h.gen.h"
#include "ip_addr.h.gen.h"

struct LoadBalancer;
struct LoadBalancer *lb_allocate_balancer(uint32_t flow_capacity,
                                          uint32_t backend_capacity,
                                          uint32_t cht_height,
                                          vigor_time_t backend_expiration_time,
                                          vigor_time_t flow_expiration_time);
struct LoadBalancedBackend lb_get_backend(struct LoadBalancer *balancer,
                                          struct LoadBalancedFlow *flow,
                                          vigor_time_t now,
                                          uint16_t wan_device);
void lb_expire_flows(struct LoadBalancer *balancer, vigor_time_t now);
void lb_expire_backends(struct LoadBalancer *balancer, vigor_time_t now);
void lb_process_heartbit(struct LoadBalancer *balancer,
                         struct LoadBalancedFlow *flow,
                         struct rte_ether_addr mac_addr, int nic, vigor_time_t now);

#endif // _LB_BALANCER_H_INCLUDED_
