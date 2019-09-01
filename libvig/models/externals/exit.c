#ifndef KLEE_VERIFICATION

#  include "nfos_halt.h"
#  include <stdio.h>

extern void exit(int exit_code);

void exit(int exit_code) {
  printf("\n\nexit(%d) called", exit_code);
  nfos_halt();
}

#endif //! KLEE_VERIFICATION
