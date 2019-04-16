#ifndef DSOS_HALT_H
#define DSOS_HALT_H

#include <stdnoreturn.h>

/* Halt the machine (spin endlessly) */
extern noreturn void dsos_halt(void) __attribute__((used));

#endif
