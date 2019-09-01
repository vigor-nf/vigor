#ifdef KLEE_VERIFICATION
#  include <stdlib.h>
#endif

#include "nfos_halt.h"

void nfos_halt(void) {

#ifdef KLEE_VERIFICATION

  exit(1); // One does not just calls "halt" if nothing bad happened

#else // KLEE_VERIFICATION

  while (1) {
    asm volatile("hlt");
  }

#endif // KLEE_VERIFICATION
}
