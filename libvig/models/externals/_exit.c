#ifndef KLEE_VERIFICATION

#  include "nfos_halt.h"
#  include <stdio.h>

void _exit(int status) {
  printf("\n\n_exit(%d) called", status);
  nfos_halt();
}

#endif //! KLEE_VERIFICATION
