#include <assert.h>
#include <time.h>

#include <klee/klee.h>
#include "nf_time.h"
#include "stubs/time_stub_control.h"
#include "kernel/dsos_tsc.h"

time_t starting_time = 0;
time_t last_time = 0;

#ifdef KLEE_VERIFICATION

__attribute__((noinline))
time_t start_time(void) {
    klee_trace_ret();
    time_t starting_time;

    struct timespec tp;
    clock_gettime(CLOCK_MONOTONIC, &tp);
    starting_time = tp.tv_sec;

    klee_assume(starting_time >= 0);
    last_time = starting_time;
    return last_time;
}

time_t restart_time(void) {
    struct timespec tp;
    clock_gettime(CLOCK_MONOTONIC, &tp);
    starting_time = tp.tv_sec;

    klee_assume(starting_time >= 0);
    last_time = starting_time;
    return last_time;
}

__attribute__((noinline))
time_t current_time(void) {
    klee_trace_ret();
    time_t next_time;

    struct timespec tp;
    clock_gettime(CLOCK_MONOTONIC, &tp);
    next_time = tp.tv_sec;

    klee_assume(last_time <= next_time);
    last_time = next_time;
    return next_time;
}

#else // KLEE_VERIFICATION

time_t restart_time(void)
{
    assert(0);
}

#endif // KLEE_VERIFICATION

time_t get_start_time_internal(void) {
    return starting_time;
}

time_t get_start_time(void) {return get_start_time_internal();}

time_t time(time_t *timer)
{
    assert(0);
}

int clock_gettime(clockid_t clk_id, struct timespec *tp)
{
    // Others not implemented
    if(clk_id != CLOCK_MONOTONIC && clk_id != CLOCK_MONOTONIC_RAW) {
      return -1;
    }

    uint64_t tsc = dsos_rdtsc();
    uint64_t freq = dsos_tsc_get_freq();

    tp->tv_nsec = (tsc * 1000000000 / freq) % 1000000000;

#ifndef KLEE_VERIFICATION
    tp->tv_sec = tsc / freq;
#else
    // HACK: Verifast doesn't like the division
    // even though there is no reason why it shouldn't
    // be correct since it's just scaling the TSC by a constant.
    // Maybe some more lemmas are needed.
    tp->tv_sec = tsc;
#endif

    return 0;
}

