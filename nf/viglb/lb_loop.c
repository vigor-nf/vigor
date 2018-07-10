#include "lb_loop.h"

#include <klee/klee.h>

#include "lib/stubs/time_stub_control.h"
#include "lib/stubs/containers/map-stub-control.h"
#include "lib/stubs/containers/vector-stub-control.h"
#include "lib/stubs/containers/double-chain-stub-control.h"


void lb_loop_iteration_assumptions(struct Map** buckets, struct Vector** heap, struct DoubleChain** indices,
                                   time_t time, uint32_t flow_capacity) {
	map_reset(*buckets);
	vector_reset(*heap);
	dchain_reset(*indices, flow_capacity);
}

void lb_loop_invariant_consume(struct Map** buckets, struct Vector** heap, struct DoubleChain** indices,
                               time_t time, uint32_t flow_capacity) {
	klee_trace_ret();
	klee_trace_param_ptr(buckets, sizeof(struct Map*), "buckets");
	klee_trace_param_ptr(heap, sizeof(struct Vector*), "heap");
	klee_trace_param_ptr(indices, sizeof(struct DoubleChain*), "indices");
	klee_trace_param_i64(time, "time");
	klee_trace_param_u32(flow_capacity, "flow_capacity");
}

void lb_loop_invariant_produce(struct Map** buckets, struct Vector** heap, struct DoubleChain** indices,
                               time_t* time, uint32_t flow_capacity) {
	klee_trace_ret();
	klee_trace_param_ptr(buckets, sizeof(struct Map*), "buckets");
	klee_trace_param_ptr(heap, sizeof(struct Vector*), "heap");
	klee_trace_param_ptr(indices, sizeof(struct DoubleChain*), "indices");
	klee_trace_param_ptr(time, sizeof(time_t), "time");
	klee_trace_param_u32(flow_capacity, "flow_capacity");

	dchain_reset(*indices, flow_capacity);
	*time = restart_time();
}

void lb_loop_iteration_begin(struct Map** buckets, struct Vector** heap, struct DoubleChain** indices,
                             time_t time, uint32_t flow_capacity) {
	lb_loop_invariant_consume(buckets, heap, indices, time, flow_capacity);
	lb_loop_invariant_produce(buckets, heap, indices, &time, flow_capacity);
}

void lb_loop_iteration_end(struct Map** buckets, struct Vector** heap, struct DoubleChain** indices,
                           time_t time, uint32_t flow_capacity) {
	lb_loop_invariant_consume(buckets, heap, indices, time, flow_capacity);
	lb_loop_invariant_produce(buckets, heap, indices, &time, flow_capacity);
}
