#include <assert.h>
#include <time.h>

#ifdef KLEE_VERIFICATION
#  include <klee/klee.h>
#endif
#include "vigor-time-control.h"

vigor_time_t starting_time = 0;
vigor_time_t last_time = 0;

#ifdef KLEE_VERIFICATION

__attribute__((noinline)) vigor_time_t start_time(void) {
  klee_trace_ret();
  vigor_time_t starting_time;
  klee_make_symbolic(&starting_time, sizeof(vigor_time_t), "starting_time");
  klee_assume(0 <= starting_time);

  last_time = starting_time;
  return last_time;
}

vigor_time_t restart_time(void) {
  klee_make_symbolic(&starting_time, sizeof(vigor_time_t), "restarting_time");
  klee_assume(0 <= starting_time);
  last_time = starting_time;
  return last_time;
}

__attribute__((noinline)) vigor_time_t current_time(void) {
  klee_trace_ret();
  vigor_time_t next_time;
  klee_make_symbolic(&next_time, sizeof(vigor_time_t), "next_time");
  klee_assume(last_time <= next_time);
  last_time = next_time;
  return next_time;
}

#else // KLEE_VERIFICATION

vigor_time_t restart_time(void) { assert(0); }

#endif // KLEE_VERIFICATION

vigor_time_t get_start_time_internal(void) { return starting_time; }

vigor_time_t get_start_time(void) { return get_start_time_internal(); }

vigor_time_t recent_time(void) {
  // Don't trace this function, it only reterns the last result of current_time
  return last_time;
}
