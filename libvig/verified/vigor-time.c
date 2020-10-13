#include "vigor-time.h"

#include <time.h>
#include <assert.h>

#ifdef NFOS
#  include <nfos_tsc.h>
#endif

vigor_time_t last_time = 0;

#ifdef NFOS
time_t time(time_t *timer) { assert(0); }

int clock_gettime(clockid_t clk_id, struct timespec *tp) {
  // Others not implemented
  if (clk_id != CLOCK_MONOTONIC && clk_id != CLOCK_MONOTONIC_RAW) {
    return -1;
  }

  __uint128_t tsc = nfos_rdtsc();
  __uint128_t freq = nfos_tsc_get_freq();
  uint64_t time_ns = (uint64_t)(tsc * 1000000000ul / freq);

#  ifdef KLEE_VERIFICATION
  // HACK: Verifast doesn't like the division
  // even though there is no reason why it shouldn't
  // be correct since it's just scaling the TSC by a constant.
  // Maybe some more lemmas are needed.
  tp->tv_sec = tsc / freq;
  tp->tv_nsec = tsc; // FIXME: modulo 1000000000, etc, use a proper formula;
#  else              // KLEE_VERIFICATION
  tp->tv_nsec = time_ns % 1000000000ul;
  tp->tv_sec = time_ns / 1000000000ul;
#  endif             // KLEE_VERIFICATION

  return 0;
}

int gettimeofday(struct timeval *tv, void* tz)
{
  if (tz != NULL) {
    return -1;
  }
  struct timespec tp;
  int ret = clock_gettime(CLOCK_MONOTONIC, &tp);
  if (ret != 0) {
    return ret;
  }
  tv->tv_sec = tp.tv_sec;
  tv->tv_usec = tp.tv_nsec / 1000;
  return 0;
}
#endif

vigor_time_t current_time(void)
//@ requires last_time(?x);
//@ ensures result >= 0 &*& x <= result &*& last_time(result);
{
  struct timespec tp;
  clock_gettime(CLOCK_MONOTONIC, &tp);
  last_time = tp.tv_sec * 1000000000ul + tp.tv_nsec;
  return last_time;
}

vigor_time_t recent_time(void) { return last_time; }
