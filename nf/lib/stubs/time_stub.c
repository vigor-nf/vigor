#include <assert.h>
#include <time.h>

#include <klee/klee.h>
#include "lib/nf_time.h"
#include "time_stub_control.h"
#include "lib/kernel/dsos_tsc.h"

vigor_time_t starting_time = 0;
vigor_time_t last_time = 0;

#ifdef KLEE_VERIFICATION

__attribute__((noinline))
vigor_time_t start_time(void) {
    klee_trace_ret();
    vigor_time_t starting_time;
    klee_make_symbolic(&starting_time, sizeof(vigor_time_t), "starting_time");

    last_time = starting_time;
    return last_time;
}

vigor_time_t restart_time(void) {
    klee_make_symbolic(&starting_time, sizeof(vigor_time_t), "restarting_time");
    last_time = starting_time;
    return last_time;
}

__attribute__((noinline))
vigor_time_t current_time(void) {
    klee_trace_ret();
    vigor_time_t next_time;
    klee_make_symbolic(&next_time, sizeof(vigor_time_t), "next_time");
    last_time = next_time;
    return next_time;
}

#else // KLEE_VERIFICATION

vigor_time_t restart_time(void)
{
    assert(0);
}

#endif // KLEE_VERIFICATION

vigor_time_t get_start_time_internal(void) {
    return starting_time;
}

vigor_time_t get_start_time(void) {return get_start_time_internal();}

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


#ifdef KLEE_VERIFICATION
    // HACK: Verifast doesn't like the division
    // even though there is no reason why it shouldn't
    // be correct since it's just scaling the TSC by a constant.
    // Maybe some more lemmas are needed.
    tp->tv_sec = tsc / freq;
    tp->tv_nsec = tsc; //FIXME: modulo 1000000000, etc, use a proper formula;
#else//KLEE_VERIFICATION
    tp->tv_nsec = (tsc * 1000000000 / freq) % 1000000000;
    tp->tv_sec = tsc / freq;
#endif//KLEE_VERIFICATION

    return 0;
}
