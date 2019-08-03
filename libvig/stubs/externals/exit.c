#ifndef KLEE_VERIFICATION

#include "dsos_halt.h"
#include <stdio.h>

extern void exit(int exit_code);

void exit(int exit_code)
{
	printf("\n\nexit(%d) called", exit_code);
	dsos_halt();
}

#endif //!KLEE_VERIFICATION
