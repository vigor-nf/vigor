/* KLEE provides its own implementation of assert() */
#ifndef KLEE_VERIFICATION

#include "dsos_halt.h"
#include "dsos_vga.h"

extern void __assert_fail(const char *msg, const char *file, int line, const char *func)
{
	dsos_vga_write_str("\n\nAssertion failed: ");
	dsos_vga_write_str(msg);
	dsos_vga_write_str(" (");
	dsos_vga_write_str(file);
	dsos_vga_write_str(": ");
	dsos_vga_write_int(line);
	dsos_vga_write_str(": ");
	dsos_vga_write_str(func);
	dsos_vga_write_str(")");

	dsos_halt();
}

#endif
