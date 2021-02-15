#include <klee/klee.h>
#include "loop.h"
#include "libvig/models/verified/vigor-time-control.h"
#include "libvig/models/verified/double-chain-control.h"
#include "libvig/models/verified/map-control.h"
#include "libvig/models/verified/vector-control.h"
void loop_reset(struct Map** fm,
                struct Vector** fv,
                struct Vector** int_devices,
                struct DoubleChain** heap,
                int max_flows,
                uint32_t fw_device,
                unsigned int lcore_id,
                vigor_time_t* time)
{
  map_reset(*fm);
  vector_reset(*fv);
  vector_reset(*int_devices);
  dchain_reset(*heap, max_flows);
  *time = restart_time();
}
void loop_invariant_consume(struct Map** fm,
                            struct Vector** fv,
                            struct Vector** int_devices,
                            struct DoubleChain** heap,
                            int max_flows,
                            uint32_t fw_device,
                            unsigned int lcore_id,
                            vigor_time_t time)
{
  klee_trace_ret();
  klee_trace_param_ptr(fm, sizeof(struct Map*), "fm");
  klee_trace_param_ptr(fv, sizeof(struct Vector*), "fv");
  klee_trace_param_ptr(int_devices, sizeof(struct Vector*), "int_devices");
  klee_trace_param_ptr(heap, sizeof(struct DoubleChain*), "heap");
  klee_trace_param_i32(max_flows, "max_flows");
  klee_trace_param_u32(fw_device, "fw_device");
  klee_trace_param_i32(lcore_id, "lcore_id");
  klee_trace_param_i64(time, "time");
}
void loop_invariant_produce(struct Map** fm,
                            struct Vector** fv,
                            struct Vector** int_devices,
                            struct DoubleChain** heap,
                            int max_flows,
                            uint32_t fw_device,
                            unsigned int* lcore_id,
                            vigor_time_t* time)
{
  klee_trace_ret();
  klee_trace_param_ptr(fm, sizeof(struct Map*), "fm");
  klee_trace_param_ptr(fv, sizeof(struct Vector*), "fv");
  klee_trace_param_ptr(int_devices, sizeof(struct Vector*), "int_devices");
  klee_trace_param_ptr(heap, sizeof(struct DoubleChain*), "heap");
  klee_trace_param_i32(max_flows, "max_flows");
  klee_trace_param_u32(fw_device, "fw_device");
  klee_trace_param_ptr(lcore_id, sizeof(unsigned int), "lcore_id");
  klee_trace_param_ptr(time, sizeof(vigor_time_t), "time");
}
void loop_iteration_border(struct Map** fm,
                           struct Vector** fv,
                           struct Vector** int_devices,
                           struct DoubleChain** heap,
                           int max_flows,
                           uint32_t fw_device,
                           unsigned int lcore_id,
                           vigor_time_t time)
{
  loop_invariant_consume(fm, fv, int_devices, heap, max_flows, fw_device, lcore_id, time);
  loop_reset(fm, fv, int_devices, heap, max_flows, fw_device, lcore_id, &time);
  loop_invariant_produce(fm, fv, int_devices, heap, max_flows, fw_device, &lcore_id, &time);
}
