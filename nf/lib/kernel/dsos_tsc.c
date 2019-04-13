#include "dsos_tsc.h"

#ifdef KLEE_VERIFICATION

extern uint64_t stub_rdtsc(void);

uint64_t dsos_rdtsc(void)
{
  return stub_rdtsc();
}

#else//KLEE_VERIFICATION

uint64_t dsos_rdtsc(void)
{
  uint64_t ret;
  asm volatile ("rdtsc" : "=A"(ret));
  return ret;
}

#endif//KLEE_VERIFICATION

uint64_t dsos_tsc_get_freq(void)
{
  /* Completely arbitrary but ok. TODO: Find a reliable way to get it from
     hardware */
  return 3599910000;
}
