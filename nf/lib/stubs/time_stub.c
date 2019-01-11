#include <assert.h>
#include <time.h>

#include <klee/klee.h>
#include "nf_time.h"
#include "stubs/time_stub_control.h"
#include "kernel/dsos_tsc.h"

time_t time(time_t *timer)
{
  assert(0);
}

time_t starting_time = 0;
time_t last_time = 0;

#ifdef KLEE_VERIFICATION

__attribute__((noinline))
time_t start_time(void) {
    klee_trace_ret();
    time_t starting_time;
    klee_make_symbolic(&starting_time, sizeof(time_t), "starting_time");
    klee_assume(starting_time >= 0);
    last_time = starting_time;
    return last_time;
}

time_t restart_time(void) {
  klee_make_symbolic(&starting_time, sizeof(time_t), "restarting_time");
  klee_assume(starting_time >= 0);
  last_time = starting_time;
  return last_time;
}

__attribute__((noinline))
time_t current_time(void) {
    klee_trace_ret();
    time_t next_time;
    klee_make_symbolic(&next_time, sizeof(time_t), "next_time");
    klee_assume(last_time <= next_time);
    last_time = next_time;
    return next_time;
}

int
clock_gettime(clockid_t clk_id, struct timespec* tp)
{
  // Not supported!
  return -1;
}

#else // KLEE_VERIFICATION

int clock_gettime(clockid_t clk_id, struct timespec *tp)
{
  // Others not implemented
  if(clk_id != CLOCK_MONOTONIC) {
    return -1;
  }

  uint64_t nsecs = dsos_rdtsc() / dsos_tsc_get_freq();

  tp->tv_nsec = nsecs % 1000000000;
  tp->tv_sec = nsecs / 1000000000;

  return 0;
  return -1;
}

time_t restart_time(void) {
  assert(0);
}

#endif

time_t get_start_time_internal(void) {
    return starting_time;
}
time_t get_start_time(void) {return get_start_time_internal();}
