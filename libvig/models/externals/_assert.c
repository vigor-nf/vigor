/* KLEE provides its own implementation of assert() */
#ifndef KLEE_VERIFICATION

#  include "nfos_halt.h"
#  include <stdio.h>

extern void __assert_fail(const char *msg, const char *file, int line,
                          const char *func) {
  printf("\n\nAssertion failed: %s (%s: %d: %s", msg, file, line, func);

  nfos_halt();
}

#endif
