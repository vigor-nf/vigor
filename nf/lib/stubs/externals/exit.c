#ifndef KLEE_VERIFICATION

#include "dsos_halt.h"
#include "dsos_vga.h"

extern void exit(int exit_code);

void exit(int exit_code)
{
	dsos_vga_write_str("\n\nexit(");
	dsos_vga_write_int(exit_code);
	dsos_vga_write_str(") called");
	dsos_halt();
}

#else

#include <klee/klee.h>

extern void exit(int exit_code);

void exit(int exit_code)
{
	klee_silent_exit(exit_code);
}

#endif
