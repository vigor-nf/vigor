#ifndef NFOS_HALT_H
#define NFOS_HALT_H

#include <stdnoreturn.h>

/* Halt the machine (spin endlessly) */
extern noreturn void nfos_halt(void) __attribute__((used));

#endif
