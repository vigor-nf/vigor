#ifndef _LB_BALANCER_H_INCLUDED_ // cannot use pragma once, included by VeriFast
#define _LB_BALANCER_H_INCLUDED_


#include "lib/nf_time.h"

#include <stdbool.h>
#include <stdint.h>


struct LoadBalancedFlow {
	uint32_t src_ip;
	uint16_t src_port;
	uint16_t dst_port;
	uint8_t protocol;
};

/*@
  inductive lb_flowi = lb_flowc(int, int, int, int);
  predicate lb_flowp(struct LoadBalancedFlow* ptr; lb_flowi flow) =
    struct_LoadBalancedFlow_padding(ptr) &*&
    ptr->src_ip |-> ?sip &*&
    ptr->src_port |-> ?sp &*&
    ptr->dst_port |-> ?dp &*&
    ptr->protocol |-> ?p &*&
    flow == lb_flowc(sip, sp, dp, p);

  fixpoint int lb_flow_hash_2(lb_flowi ea);
@*/


bool lb_flow_equality(void* objA, void* objB);
/*@ requires [?fr1]lb_flowp(objA, ?f1) &*&
             [?fr2]lb_flowp(objB, ?f2); @*/
/*@ ensures [fr1]lb_flowp(objA, f1) &*&
            [fr2]lb_flowp(objB, f2) &*&
            (result ? (f1 == f2) : (f1 != f2)); @*/

int lb_flow_hash(void* obj);
/*@ requires [?fr]lb_flowp(obj, ?f); @*/
/*@ ensures [fr]lb_flowp(obj, f) &*&
            result == lb_flow_hash_2(f); @*/

void lb_flow_init(void* obj);
/*@ requires chars(obj, sizeof(struct LoadBalancedFlow), _); @*/
/*@ ensures lb_flowp(obj, _); @*/


struct LoadBalancer;
struct LoadBalancer* lb_allocate_balancer(uint32_t flow_capacity, uint32_t flow_expiration_time, uint16_t backend_count);
uint16_t lb_get_backend(struct LoadBalancer* balancer, struct LoadBalancedFlow* flow, time_t now);
void lb_expire_flows(struct LoadBalancer* balancer, time_t now);

#ifdef KLEE_VERIFICATION
struct Map** lb_get_buckets(struct LoadBalancer* balancer);
struct Vector** lb_get_heap(struct LoadBalancer* balancer);
struct DoubleChain** lb_get_indices(struct LoadBalancer* balancer);
#endif


#endif // _LB_BALANCER_H_INCLUDED_
