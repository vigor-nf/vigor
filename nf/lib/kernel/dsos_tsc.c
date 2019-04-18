#include "dsos_tsc.h"
#include <x86intrin.h>

#ifdef KLEE_VERIFICATION

extern uint64_t stub_rdtsc(void);

uint64_t dsos_rdtsc(void)
{
  return stub_rdtsc();
}

#else//KLEE_VERIFICATION

uint64_t dsos_rdtsc(void)
{
	return __rdtsc();
}

#endif//KLEE_VERIFICATION

uint64_t dsos_tsc_get_freq(void)
{
  /* Completely arbitrary but ok. TODO: Find a reliable way to get it from
     hardware */
  return 3599910000;
}
