#include <string.h>
#include "lb_balancer.h"

#ifdef KLEE_VERIFICATION
#  define AND &
#else//KLEE_VERIFICATION
#  define AND &&
#endif//KLEE_VERIFICATION

#ifdef KLEE_VERIFICATION

#define FIELD(struct_name, name, size) { offsetof(struct struct_name, name), sizeof(size), #name }
#define FFIELD(name, size) FIELD(LoadBalancedFlow, name, size)
#define BFIELD(name, size) FIELD(LoadBalancedBackend, name, size)

struct str_field_descr lb_flow_fields[] = {
	FFIELD(src_ip, uint32_t), FFIELD(dst_ip, uint32_t),
  FFIELD(src_port, uint16_t), FFIELD(dst_port, uint16_t),
  FFIELD(protocol, uint8_t)
};

struct str_field_descr lb_backend_fields[] = {
	BFIELD(nic, uint16_t),
  {offsetof(struct LoadBalancedBackend, mac), sizeof(struct ether_addr), "mac"},
	BFIELD(ip, uint32_t)
};

struct nested_field_descr lb_backend_nested_fields[] = {
  {offsetof(struct LoadBalancedBackend, mac), 0, 6 * sizeof(uint8_t), "addr_bytes"},
};

#undef BFIELD
#undef FFIELD
#undef FIELD

int lb_flow_fields_number() {
  return sizeof(lb_flow_fields)/sizeof(lb_flow_fields[0]);
}

int lb_backend_fields_number() {
  return sizeof(lb_backend_fields)/sizeof(lb_backend_fields[0]);
}

int lb_backend_nested_fields_number() {
  return sizeof(lb_backend_nested_fields)/sizeof(lb_backend_nested_fields[0]);
}
#endif//KLEE_VERIFICATION

bool
lb_flow_equality(void* objA, void* objB)
/*@ requires [?fr1]lb_flowp(objA, ?f1) &*&
             [?fr2]lb_flowp(objB, ?f2); @*/
/*@ ensures [fr1]lb_flowp(objA, f1) &*&
            [fr2]lb_flowp(objB, f2) &*&
            (result ? (f1 == f2) : (f1 != f2)); @*/
{
	struct LoadBalancedFlow* flowA = objA;
	struct LoadBalancedFlow* flowB = objB;

	return flowA->src_ip == flowB->src_ip
    AND flowA->src_port == flowB->src_port
    AND flowA->dst_port == flowB->dst_port
    AND flowA->protocol == flowB->protocol;
}

#ifdef KLEE_VERIFICATION
#include <klee/klee.h>
uint32_t
lb_flow_hash(void* obj)
{
  klee_trace_ret();
  klee_trace_param_tagged_ptr(obj, sizeof(struct LoadBalancedFlow),
                              "obj", "LoadBalancedFlow", TD_BOTH);
  {
    for (int i = 0; i < lb_flow_fields_number(); ++i) {
      klee_trace_param_ptr_field(obj,
                                 lb_flow_fields[i].offset,
                                 lb_flow_fields[i].width,
                                 lb_flow_fields[i].name);
    }
  }
	return klee_int("flow_hash");
}
#else//KLEE_VERIFICATION
uint32_t
lb_flow_hash(void* obj)
/*@ requires [?fr]lb_flowp(obj, ?f); @*/
/*@ ensures [fr]lb_flowp(obj, f) &*&
            result == lb_flow_hash_2(f); @*/
{
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
#endif//KLEE_VERIFICATION

void
lb_flow_init(void* obj)
/*@ requires chars(obj, sizeof(struct LoadBalancedFlow), _); @*/
/*@ ensures lb_flowp(obj, _); @*/
{
	memset(obj, 0, sizeof(struct LoadBalancedFlow));
}

void
lb_backend_init(void* obj)
/*@ requires chars(obj, sizeof(struct LoadBalancedBackend), _); @*/
/*@ ensures lb_backendp(obj, _); @*/
{
	memset(obj, 0, sizeof(struct LoadBalancedBackend));
}

bool lb_ip_equality(void* objA, void* objB)
/*@ requires [?fr1]u_integer(objA, ?f1) &*&
             [?fr2]u_integer(objB, ?f2); @*/
/*@ ensures [fr1]u_integer(objA, f1) &*&
            [fr2]u_integer(objB, f2) &*&
            (result ? (f1 == f2) : (f1 != f2)); @*/
{
  return *(uint32_t*)objA == *(uint32_t*)objB;
}

uint32_t lb_ip_hash(void* obj)
/*@ requires [?fr]u_integer(obj, ?f); @*/
/*@ ensures [fr]u_integer(obj, f) &*&
            result == lb_ip_hash_fp(f); @*/
{
  return *(uint32_t*)obj;
}
