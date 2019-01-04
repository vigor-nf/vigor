#include <klee/klee.h>
#include "nat_loop.h"
#include "lib/stubs/time_stub_control.h"
#include "lib/stubs/containers/double-chain-stub-control.h"
#include "lib/stubs/containers/map-stub-control.h"
#include "lib/stubs/containers/vector-stub-control.h"

void loop_iteration_assumptions(struct Map** m,
                                struct Vector** v,
                                struct DoubleChain** ch,
                                unsigned int lcore_id,
                                time_t time, int max_flows, int start_port)
{
  map_reset(*m);
  vector_reset(*v);
  dchain_reset(*ch, max_flows);
}

void loop_iteration_assertions(struct Map** m,
                               struct Vector** v,
                               struct DoubleChain** ch,
                               unsigned int lcore_id,
                               time_t time, int max_flows, int start_port)
{

}

__attribute__((noinline))
void loop_invariant_consume(struct Map** m,
                            struct Vector** v,
                            struct DoubleChain** ch,
                            unsigned int lcore_id,
                            time_t time, int max_flows, int start_port)
{
  klee_trace_ret();
  klee_trace_param_ptr(m, sizeof(struct Map*), "m");
  klee_trace_param_ptr(v, sizeof(struct Vector*), "v");
  klee_trace_param_ptr(ch, sizeof(struct DoubleChain*), "ch");
  klee_trace_param_i32(lcore_id, "lcore_id");
  klee_trace_param_i64(time, "time");
  klee_trace_param_i32(max_flows, "max_flows");
  klee_trace_param_i32(start_port, "start_port");
}

__attribute__((noinline))
void loop_invariant_produce(struct Map** m,
                            struct Vector** v,
                            struct DoubleChain** ch,
                            unsigned int* lcore_id,
                            time_t *time, int max_flows, int start_port)
{
  klee_trace_ret();
  klee_trace_param_ptr(m, sizeof(struct Map*), "m");
  klee_trace_param_ptr(v, sizeof(struct Vector*), "v");
  klee_trace_param_ptr(ch, sizeof(struct DoubleChain*), "ch");
  klee_trace_param_ptr(lcore_id, sizeof(unsigned int), "lcore_id");
  klee_trace_param_ptr(time, sizeof(time_t), "time");
  klee_trace_param_i32(max_flows, "max_flows");
  klee_trace_param_i32(start_port, "start_port");
  dchain_reset(*ch, max_flows);
  *time = restart_time();
}

void loop_iteration_begin(struct Map** m,
                          struct Vector** v,
                          struct DoubleChain** ch,
                          unsigned int lcore_id,
                          time_t time, int max_flows, int start_port) {
  loop_invariant_consume(m, v, ch, lcore_id,
                         time, max_flows, start_port);
  loop_invariant_produce(m, v, ch, &lcore_id,
                         &time, max_flows, start_port);
}

void loop_iteration_end(struct Map** m,
                        struct Vector** v,
                        struct DoubleChain** ch,
                        unsigned int lcore_id,
                        time_t time, int max_flows, int start_port) {
  loop_invariant_consume(m, v, ch, lcore_id,
                         time, max_flows, start_port);
  loop_invariant_produce(m, v, ch, &lcore_id,
                         &time, max_flows, start_port);
}

void loop_enumeration_begin(struct Map** m,
                            struct Vector** v,
                            struct DoubleChain** ch,
                            unsigned int lcore_id,
                            time_t time, int max_flows, int start_port,
                            int cnt)
{
  (void)cnt;
  loop_invariant_consume(m, v, ch, lcore_id,
                         time, max_flows, start_port);
  loop_invariant_produce(m, v, ch, &lcore_id,
                         &time, max_flows, start_port);
}

void loop_enumeration_end(struct Map** m,
                          struct Vector** v,
                          struct DoubleChain** ch,
                          unsigned int lcore_id,
                          time_t time, int max_flows, int start_port)
{
  loop_invariant_consume(m, v, ch, lcore_id,
                         time, max_flows, start_port);
  loop_invariant_produce(m, v, ch, &lcore_id,
                         &time, max_flows, start_port);
}
