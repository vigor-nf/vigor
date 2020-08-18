#include <klee/klee.h>
#include "loop.h"
#include "libvig/models/verified/vigor-time-control.h"
#include "libvig/models/verified/double-chain-control.h"
#include "libvig/models/verified/map-control.h"
#include "libvig/models/verified/vector-control.h"
void loop_reset(unsigned int lcore_id,
                vigor_time_t* time)
{
  *time = restart_time();
}
void loop_invariant_consume(unsigned int lcore_id,
                            vigor_time_t time)
{
  klee_trace_ret();
  klee_trace_param_i32(lcore_id, "lcore_id");
  klee_trace_param_i64(time, "time");
}
void loop_invariant_produce(unsigned int* lcore_id,
                            vigor_time_t* time)
{
  klee_trace_ret();
  klee_trace_param_ptr(lcore_id, sizeof(unsigned int), "lcore_id");
  klee_trace_param_ptr(time, sizeof(vigor_time_t), "time");
}
void loop_iteration_border(unsigned int lcore_id,
                           vigor_time_t time)
{
  loop_invariant_consume(lcore_id, time);
  loop_reset(lcore_id, &time);
  loop_invariant_produce(&lcore_id, &time);
}
