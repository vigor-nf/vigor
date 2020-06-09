#ifndef KLEE_VERIFICATION

#  include <stdlib.h>

#  include <nfos_halt.h>
#  include <stdio.h>

void abort(void) {
  printf("\n\nabort() called");
  nfos_halt();
}

#endif //! KLEE_VERIFICATION
