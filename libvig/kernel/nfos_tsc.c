#include "nfos_tsc.h"
#include <x86intrin.h>
#include <rte_cycles.h>

#ifdef KLEE_VERIFICATION

extern uint64_t stub_rdtsc(void);

uint64_t nfos_rdtsc(void) { return stub_rdtsc(); }

#else // KLEE_VERIFICATION

uint64_t nfos_rdtsc(void) { return __rdtsc(); }

#endif // KLEE_VERIFICATION

uint64_t nfos_tsc_get_freq(void) { return rte_get_tsc_hz(); }
