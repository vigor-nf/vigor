#ifdef KLEE_VERIFICATION
#include <stdlib.h>
#endif

#include "dsos_halt.h"

void dsos_halt(void)
{
#ifndef KLEE_VERIFICATION
	while(1) {
		asm volatile("hlt");
	}
#else
	exit(0);
#endif
}
