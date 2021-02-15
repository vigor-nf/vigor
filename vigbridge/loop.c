#include <klee/klee.h>
#include "loop.h"
#include "libvig/models/verified/vigor-time-control.h"
#include "libvig/models/verified/double-chain-control.h"
#include "libvig/models/verified/map-control.h"
#include "libvig/models/verified/vector-control.h"
void loop_reset(struct Map** dyn_map,
                struct Vector** dyn_keys,
                struct Vector** dyn_vals,
                struct Map** st_map,
                struct Vector** st_vec,
                struct DoubleChain** dyn_heap,
                uint32_t capacity,
                uint32_t stat_capacity,
                uint32_t dev_count,
                unsigned int lcore_id,
                vigor_time_t* time)
{
  map_reset(*dyn_map);
  vector_reset(*dyn_keys);
  vector_reset(*dyn_vals);
  map_reset(*st_map);
  vector_reset(*st_vec);
  dchain_reset(*dyn_heap, capacity);
  *time = restart_time();
}
void loop_invariant_consume(struct Map** dyn_map,
                            struct Vector** dyn_keys,
                            struct Vector** dyn_vals,
                            struct Map** st_map,
                            struct Vector** st_vec,
                            struct DoubleChain** dyn_heap,
                            uint32_t capacity,
                            uint32_t stat_capacity,
                            uint32_t dev_count,
                            unsigned int lcore_id,
                            vigor_time_t time)
{
  klee_trace_ret();
  klee_trace_param_ptr(dyn_map, sizeof(struct Map*), "dyn_map");
  klee_trace_param_ptr(dyn_keys, sizeof(struct Vector*), "dyn_keys");
  klee_trace_param_ptr(dyn_vals, sizeof(struct Vector*), "dyn_vals");
  klee_trace_param_ptr(st_map, sizeof(struct Map*), "st_map");
  klee_trace_param_ptr(st_vec, sizeof(struct Vector*), "st_vec");
  klee_trace_param_ptr(dyn_heap, sizeof(struct DoubleChain*), "dyn_heap");
  klee_trace_param_u32(capacity, "capacity");
  klee_trace_param_u32(stat_capacity, "stat_capacity");
  klee_trace_param_u32(dev_count, "dev_count");
  klee_trace_param_i32(lcore_id, "lcore_id");
  klee_trace_param_i64(time, "time");
}
void loop_invariant_produce(struct Map** dyn_map,
                            struct Vector** dyn_keys,
                            struct Vector** dyn_vals,
                            struct Map** st_map,
                            struct Vector** st_vec,
                            struct DoubleChain** dyn_heap,
                            uint32_t capacity,
                            uint32_t stat_capacity,
                            uint32_t dev_count,
                            unsigned int* lcore_id,
                            vigor_time_t* time)
{
  klee_trace_ret();
  klee_trace_param_ptr(dyn_map, sizeof(struct Map*), "dyn_map");
  klee_trace_param_ptr(dyn_keys, sizeof(struct Vector*), "dyn_keys");
  klee_trace_param_ptr(dyn_vals, sizeof(struct Vector*), "dyn_vals");
  klee_trace_param_ptr(st_map, sizeof(struct Map*), "st_map");
  klee_trace_param_ptr(st_vec, sizeof(struct Vector*), "st_vec");
  klee_trace_param_ptr(dyn_heap, sizeof(struct DoubleChain*), "dyn_heap");
  klee_trace_param_u32(capacity, "capacity");
  klee_trace_param_u32(stat_capacity, "stat_capacity");
  klee_trace_param_u32(dev_count, "dev_count");
  klee_trace_param_ptr(lcore_id, sizeof(unsigned int), "lcore_id");
  klee_trace_param_ptr(time, sizeof(vigor_time_t), "time");
}
void loop_iteration_border(struct Map** dyn_map,
                           struct Vector** dyn_keys,
                           struct Vector** dyn_vals,
                           struct Map** st_map,
                           struct Vector** st_vec,
                           struct DoubleChain** dyn_heap,
                           uint32_t capacity,
                           uint32_t stat_capacity,
                           uint32_t dev_count,
                           unsigned int lcore_id,
                           vigor_time_t time)
{
  loop_invariant_consume(dyn_map, dyn_keys, dyn_vals, st_map, st_vec, dyn_heap, capacity, stat_capacity, dev_count, lcore_id, time);
  loop_reset(dyn_map, dyn_keys, dyn_vals, st_map, st_vec, dyn_heap, capacity, stat_capacity, dev_count, lcore_id, &time);
  loop_invariant_produce(dyn_map, dyn_keys, dyn_vals, st_map, st_vec, dyn_heap, capacity, stat_capacity, dev_count, &lcore_id, &time);
}
