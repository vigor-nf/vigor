#include "nf_time.h"

#include <time.h>

vigor_time_t last_time = 0;

vigor_time_t current_time(void)
//@ requires last_time(?x);
//@ ensures result >= 0 &*& x <= result &*& last_time(result);
{
  struct timespec tp;
  clock_gettime(CLOCK_MONOTONIC, &tp);
  last_time = tp.tv_sec * 1000000000 + tp.tv_nsec;
  return last_time;
}

vigor_time_t recent_time(void)
{
  return last_time;
}
