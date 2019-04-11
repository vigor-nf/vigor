#ifndef DSOS_TSC_H
#define DSOS_TSC_H

#include <stdint.h>

extern uint64_t dsos_rdtsc(void);
extern uint64_t dsos_tsc_get_freq(void);

#endif
