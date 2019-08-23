#ifndef KLEE_VERIFICATION

#  include <stdlib.h>

#  include <dsos_halt.h>
#  include <stdio.h>

void abort(void) {
  printf("\n\nabort() called");
  dsos_halt();
}

#endif //! KLEE_VERIFICATION
