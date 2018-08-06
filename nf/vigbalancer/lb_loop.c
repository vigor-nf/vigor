#include "lb_loop.h"

#include <klee/klee.h>

#include "lib/stubs/time_stub_control.h"
#include "lib/stubs/containers/map-stub-control.h"
#include "lib/stubs/containers/vector-stub-control.h"
#include "lib/stubs/containers/double-chain-stub-control.h"


void lb_loop_iteration_assumptions(struct Map** indices, struct Vector** heap, struct Vector** backends, struct DoubleChain** chain,
                                   time_t time, uint32_t flow_capacity) {
	map_reset(*indices);
	vector_reset(*heap);
	vector_reset(*backends);
	dchain_reset(*chain, flow_capacity);
}

void lb_loop_invariant_consume(struct Map** indices, struct Vector** heap, struct Vector** backends, struct DoubleChain** chain,
                               time_t time, uint32_t flow_capacity) {
	klee_trace_ret();
	klee_trace_param_ptr(indices, sizeof(struct Map*), "indices");
	klee_trace_param_ptr(heap, sizeof(struct Vector*), "heap");
	klee_trace_param_ptr(backends, sizeof(struct Vector*), "backends");
	klee_trace_param_ptr(chain, sizeof(struct DoubleChain*), "chain");
	klee_trace_param_i64(time, "time");
	klee_trace_param_u32(flow_capacity, "flow_capacity");
}

void lb_loop_invariant_produce(struct Map** indices, struct Vector** heap, struct Vector** backends, struct DoubleChain** chain,
                               time_t* time, uint32_t flow_capacity) {
	klee_trace_ret();
	klee_trace_param_ptr(indices, sizeof(struct Map*), "indices");
	klee_trace_param_ptr(heap, sizeof(struct Vector*), "heap");
	klee_trace_param_ptr(backends, sizeof(struct Vector*), "backends");
	klee_trace_param_ptr(chain, sizeof(struct DoubleChain*), "chain");
	klee_trace_param_ptr(time, sizeof(time_t), "time");
	klee_trace_param_u32(flow_capacity, "flow_capacity");

	lb_loop_iteration_assumptions(indices, heap, backends, chain, *time, flow_capacity);
	*time = restart_time();
}

void lb_loop_iteration_begin(struct Map** indices, struct Vector** heap, struct Vector** backends, struct DoubleChain** chain,
                             time_t time, uint32_t flow_capacity) {
	lb_loop_invariant_consume(indices, heap, backends, chain, time, flow_capacity);
	lb_loop_invariant_produce(indices, heap, backends, chain, &time, flow_capacity);
}

void lb_loop_iteration_end(struct Map** indices, struct Vector** heap, struct Vector** backends, struct DoubleChain** chain,
                           time_t time, uint32_t flow_capacity) {
	lb_loop_invariant_consume(indices, heap, backends, chain, time, flow_capacity);
	lb_loop_invariant_produce(indices, heap, backends, chain, &time, flow_capacity);
}
