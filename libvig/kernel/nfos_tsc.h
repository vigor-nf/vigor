#ifndef NFOS_TSC_H
#define NFOS_TSC_H

#include <stdint.h>

extern uint64_t nfos_rdtsc(void);
extern uint64_t nfos_tsc_get_freq(void);

#endif
