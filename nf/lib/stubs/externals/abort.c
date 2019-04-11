#ifndef KLEE_VERIFICATION

#include <stdlib.h>

#include <dsos_halt.h>
#include <dsos_vga.h>

void abort(void)
{
	dsos_vga_write_str("\n\nabort() called");
	dsos_halt();
}

#else //!KLEE_VERIFICATION

/* #include <klee/klee.h> */
/* #include <stdlib.h> */

/* void abort(void) */
/* { */
/* 	klee_abort(); */
/* } */

#endif //!KLEE_VERIFICATION
