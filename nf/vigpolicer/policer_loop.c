#include <klee/klee.h>
#include "policer_loop.h"
#include "lib/stubs/containers/double-chain-stub-control.h"
#include "lib/stubs/containers/map-stub-control.h"
#include "lib/stubs/containers/vector-stub-control.h"
#include "lib/stubs/time_stub_control.h"




void policer_loop_iteration_assumptions(struct DoubleChain** dyn_heap,
                                       struct Map** dyn_map,
                                       struct Vector** dyn_keys,
                                       struct Vector** dyn_vals,
                                       uint32_t capacity,
                                       time_t time) {
  dchain_reset(*dyn_heap, capacity);
  map_reset(*dyn_map);
  vector_reset(*dyn_keys);
  vector_reset(*dyn_vals);
}

void policer_loop_invariant_consume(struct DoubleChain** dyn_heap,
                                   struct Map** dyn_map,
                                   struct Vector** dyn_keys,
                                   struct Vector** dyn_vals,
                                   uint32_t capacity,
                                   time_t time,
                                   uint32_t dev_count) {
  klee_trace_ret();
  klee_trace_param_ptr(dyn_heap, sizeof(struct DoubleChain*), "dyn_heap");
  klee_trace_param_ptr(dyn_map, sizeof(struct Map*), "dyn_map");
  klee_trace_param_ptr(dyn_keys, sizeof(struct Vector*), "dyn_keys");
  klee_trace_param_ptr(dyn_vals, sizeof(struct Vector*), "dyn_vals");
  klee_trace_param_i32(capacity, "capacity");
  klee_trace_param_i32(time, "time");
  klee_trace_param_i32(dev_count, "dev_count");
}


void policer_loop_invariant_produce(struct DoubleChain** dyn_heap,
                                   struct Map** dyn_map,
                                   struct Vector** dyn_keys,
                                   struct Vector** dyn_vals,
                                   uint32_t capacity,
                                   time_t* time,
                                   uint32_t dev_count) {
  klee_trace_ret();
  klee_trace_param_ptr(dyn_heap, sizeof(struct DoubleChain*), "dyn_heap");
  klee_trace_param_ptr(dyn_map, sizeof(struct Map*), "dyn_map");
  klee_trace_param_ptr(dyn_keys, sizeof(struct Vector*), "dyn_keys");
  klee_trace_param_ptr(dyn_vals, sizeof(struct Vector*), "dyn_vals");
  klee_trace_param_i32(capacity, "capacity");
  klee_trace_param_ptr(time, sizeof(uint32_t), "time");
  klee_trace_param_i32(dev_count, "dev_count");
  policer_loop_iteration_assumptions(dyn_heap, dyn_map, dyn_keys, dyn_vals,
                                    capacity,
                                    *time);
  *time = restart_time();
}

void policer_loop_iteration_begin(struct DoubleChain** dyn_heap,
                                 struct Map** dyn_map,
                                 struct Vector** dyn_keys,
                                 struct Vector** dyn_vals,
                                 uint32_t capacity,
                                 time_t time,
                                 uint16_t dev_count) {
  policer_loop_invariant_consume(dyn_heap, dyn_map, dyn_keys, dyn_vals,
                                capacity,
                                time, dev_count);
  policer_loop_invariant_produce(dyn_heap, dyn_map, dyn_keys, dyn_vals,
                                capacity,
                                &time, dev_count);
}

void policer_loop_iteration_end(struct DoubleChain** dyn_heap,
                               struct Map** dyn_map,
                               struct Vector** dyn_keys,
                               struct Vector** dyn_vals,
                               uint32_t capacity,
                               time_t time,
                               uint16_t dev_count) {
  policer_loop_invariant_consume(dyn_heap, dyn_map, dyn_keys, dyn_vals,
                                capacity,
                                time, dev_count);
  policer_loop_invariant_produce(dyn_heap, dyn_map, dyn_keys, dyn_vals,
                                capacity,
                                &time, dev_count);
}
