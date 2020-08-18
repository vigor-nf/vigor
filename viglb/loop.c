#include <klee/klee.h>
#include "loop.h"
#include "libvig/models/verified/vigor-time-control.h"
#include "libvig/models/verified/double-chain-control.h"
#include "libvig/models/verified/map-control.h"
#include "libvig/models/verified/vector-control.h"
void loop_reset(struct Map** flow_to_flow_id,
                struct Vector** flow_heap,
                struct DoubleChain** flow_chain,
                struct Vector** flow_id_to_backend_id,
                struct Map** ip_to_backend_id,
                struct Vector** backend_ips,
                struct Vector** backends,
                struct DoubleChain** active_backends,
                struct Vector** cht,
                uint32_t backend_capacity,
                uint32_t flow_capacity,
                uint32_t cht_height,
                unsigned int lcore_id,
                vigor_time_t* time)
{
  map_reset(*flow_to_flow_id);
  vector_reset(*flow_heap);
  dchain_reset(*flow_chain, flow_capacity);
  vector_reset(*flow_id_to_backend_id);
  map_reset(*ip_to_backend_id);
  vector_reset(*backend_ips);
  vector_reset(*backends);
  dchain_reset(*active_backends, backend_capacity);
  vector_reset(*cht);
  *time = restart_time();
}
void loop_invariant_consume(struct Map** flow_to_flow_id,
                            struct Vector** flow_heap,
                            struct DoubleChain** flow_chain,
                            struct Vector** flow_id_to_backend_id,
                            struct Map** ip_to_backend_id,
                            struct Vector** backend_ips,
                            struct Vector** backends,
                            struct DoubleChain** active_backends,
                            struct Vector** cht,
                            uint32_t backend_capacity,
                            uint32_t flow_capacity,
                            uint32_t cht_height,
                            unsigned int lcore_id,
                            vigor_time_t time)
{
  klee_trace_ret();
  klee_trace_param_ptr(flow_to_flow_id, sizeof(struct Map*), "flow_to_flow_id");
  klee_trace_param_ptr(flow_heap, sizeof(struct Vector*), "flow_heap");
  klee_trace_param_ptr(flow_chain, sizeof(struct DoubleChain*), "flow_chain");
  klee_trace_param_ptr(flow_id_to_backend_id, sizeof(struct Vector*), "flow_id_to_backend_id");
  klee_trace_param_ptr(ip_to_backend_id, sizeof(struct Map*), "ip_to_backend_id");
  klee_trace_param_ptr(backend_ips, sizeof(struct Vector*), "backend_ips");
  klee_trace_param_ptr(backends, sizeof(struct Vector*), "backends");
  klee_trace_param_ptr(active_backends, sizeof(struct DoubleChain*), "active_backends");
  klee_trace_param_ptr(cht, sizeof(struct Vector*), "cht");
  klee_trace_param_u32(backend_capacity, "backend_capacity");
  klee_trace_param_u32(flow_capacity, "flow_capacity");
  klee_trace_param_u32(cht_height, "cht_height");
  klee_trace_param_i32(lcore_id, "lcore_id");
  klee_trace_param_i64(time, "time");
}
void loop_invariant_produce(struct Map** flow_to_flow_id,
                            struct Vector** flow_heap,
                            struct DoubleChain** flow_chain,
                            struct Vector** flow_id_to_backend_id,
                            struct Map** ip_to_backend_id,
                            struct Vector** backend_ips,
                            struct Vector** backends,
                            struct DoubleChain** active_backends,
                            struct Vector** cht,
                            uint32_t backend_capacity,
                            uint32_t flow_capacity,
                            uint32_t cht_height,
                            unsigned int* lcore_id,
                            vigor_time_t* time)
{
  klee_trace_ret();
  klee_trace_param_ptr(flow_to_flow_id, sizeof(struct Map*), "flow_to_flow_id");
  klee_trace_param_ptr(flow_heap, sizeof(struct Vector*), "flow_heap");
  klee_trace_param_ptr(flow_chain, sizeof(struct DoubleChain*), "flow_chain");
  klee_trace_param_ptr(flow_id_to_backend_id, sizeof(struct Vector*), "flow_id_to_backend_id");
  klee_trace_param_ptr(ip_to_backend_id, sizeof(struct Map*), "ip_to_backend_id");
  klee_trace_param_ptr(backend_ips, sizeof(struct Vector*), "backend_ips");
  klee_trace_param_ptr(backends, sizeof(struct Vector*), "backends");
  klee_trace_param_ptr(active_backends, sizeof(struct DoubleChain*), "active_backends");
  klee_trace_param_ptr(cht, sizeof(struct Vector*), "cht");
  klee_trace_param_u32(backend_capacity, "backend_capacity");
  klee_trace_param_u32(flow_capacity, "flow_capacity");
  klee_trace_param_u32(cht_height, "cht_height");
  klee_trace_param_ptr(lcore_id, sizeof(unsigned int), "lcore_id");
  klee_trace_param_ptr(time, sizeof(vigor_time_t), "time");
}
void loop_iteration_border(struct Map** flow_to_flow_id,
                           struct Vector** flow_heap,
                           struct DoubleChain** flow_chain,
                           struct Vector** flow_id_to_backend_id,
                           struct Map** ip_to_backend_id,
                           struct Vector** backend_ips,
                           struct Vector** backends,
                           struct DoubleChain** active_backends,
                           struct Vector** cht,
                           uint32_t backend_capacity,
                           uint32_t flow_capacity,
                           uint32_t cht_height,
                           unsigned int lcore_id,
                           vigor_time_t time)
{
  loop_invariant_consume(flow_to_flow_id, flow_heap, flow_chain, flow_id_to_backend_id, ip_to_backend_id, backend_ips, backends, active_backends, cht, backend_capacity, flow_capacity, cht_height, lcore_id, time);
  loop_reset(flow_to_flow_id, flow_heap, flow_chain, flow_id_to_backend_id, ip_to_backend_id, backend_ips, backends, active_backends, cht, backend_capacity, flow_capacity, cht_height, lcore_id, &time);
  loop_invariant_produce(flow_to_flow_id, flow_heap, flow_chain, flow_id_to_backend_id, ip_to_backend_id, backend_ips, backends, active_backends, cht, backend_capacity, flow_capacity, cht_height, &lcore_id, &time);
}
