#include <assert.h>
#include <stddef.h>
#include <stdio.h>

#include "dsos_pci.h"
#include "dsos_msr.h"
#include "dsos_halt.h"
#include "dsos_vga.h"
#include "dsos_serial.h"

extern void _init(void);
extern void do_map_test(void);

/* Kernel main */
extern int main(void);
/* NF main */
extern int nf_main(int argc, char *argv[]);
/* Initialize filesystem */
extern void stub_stdio_files_init(struct dsos_pci_nic *devs, int n);
/* Start and end of constructor list */
extern int __CTORS_START, __CTORS_END;

#ifdef VIGOR_STUB_HARDWARE
extern struct dsos_pci_nic *stub_hardware_get_nics(int *n);
#endif

int main(void)
{
// 	static char *argv[] = {
// 		"vignat", "--no-shconf",
// 		"--",
// 		"--lan-dev", "0",
// 		"--wan", "1",
// 		"--expire", "60",
// 		"--starting-port", "0",
// 		"--max-flows", "65536",
// #ifdef VIGOR_STUB_HARDWARE
// 		"--extip", "0.0.0.0",
// 		"--eth-dest", "0,01:23:45:67:89:00",
// 		"--eth-dest", "1,01:23:45:67:89:01",
// #else
// 		"--extip", "192.168.4.2",
// 		"--eth-dest", "0,90:e2:ba:55:15:5c",
// 		"--eth-dest", "1,90:e2:ba:55:15:5d",
// #endif
// 		NULL,
// 	};

	static char *argv[] = {
		"vigbridge", "--no-shconf",
		"--",
		"--expire", "60",
		"--capacity", "65536",
		NULL,
	};

	static const int argc = (sizeof(argv) / sizeof(argv[0])) - 1;

	dsos_serial_init();

	int num_devs;
	struct dsos_pci_nic *devs;

#ifdef VIGOR_STUB_HARDWARE
	devs = stub_hardware_get_nics(&num_devs);
#else
	devs = dsos_pci_find_nics(&num_devs);
#endif

	if (devs == NULL) {
		dsos_vga_write_str("Error getting PCI devices\n");
		return -1;
	}

	stub_stdio_files_init(devs, num_devs);

	_init();

#ifndef KLEE_VERIFICATION
	/* Yeah maybe this isn't the best way to call constructors but it should work */

	/* Pointer to a function with no argument and no return value */
	// void (**ctor)(void) = (void (**)(void))&__CTORS_START;
	// void (**ctors_end)(void) = (void (**)(void))&__CTORS_END;

	// while (ctor != ctors_end) {
	// 	(*ctor)();
	// 	ctor++;
	// }
#endif

	// do_map_test();

	dsos_vga_write_str("Calling NAT...\n");
	nf_main(argc, argv);
	dsos_vga_write_str("Done\n");

	return 0;
}
