#include <assert.h>
#include <stddef.h>
#include <stdio.h>

#include "nfos_pci.h"
#include "nfos_halt.h"
#include "nfos_serial.h"

extern void _init(void);
extern void do_map_test(void);

/* Kernel main */
extern int main(void);
/* NF main */
extern int nf_main(int argc, char *argv[]);
/* Initialize filesystem */
extern void stub_stdio_files_init(struct nfos_pci_nic *devs, int n);

#ifdef VIGOR_MODEL_HARDWARE
extern struct nfos_pci_nic *stub_hardware_get_nics(int *n);
#endif

int main(void) {
  static char *argv[] = {
    NF_ARGUMENTS,
    NULL,
  };

  static const int argc = (sizeof(argv) / sizeof(argv[0])) - 1;

#ifndef KLEE_VERIFICATION
  nfos_serial_init();
#endif //! KLEE_VERIFICATION

  int num_devs;
  struct nfos_pci_nic *devs;

#ifdef VIGOR_MODEL_HARDWARE
  devs = stub_hardware_get_nics(&num_devs);
#else  // VIGOR_MODEL_HARDWARE
  devs = nfos_pci_find_nics(&num_devs);
#endif // VIGOR_MODEL_HARDWARE

  stub_stdio_files_init(devs, num_devs);

#ifndef KLEE_VERIFICATION
  _init();
#endif //! KLEE_VERIFICATION

  printf("Calling NF...\n");
  nf_main(argc, argv);
  printf("Done\n");

  return 0;
}
