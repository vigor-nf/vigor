#ifndef NFOS_PCI_H
#define NFOS_PCI_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define PCI_NUM_RESOURCES 6

struct nfos_pci_resource {
  void *start;
  size_t size;
  bool is_mem;
};

struct nfos_pci_nic {
  uint16_t vendor_id;
  uint16_t device_id;

  uint16_t subsystem_id;
  uint16_t subsystem_vendor_id;

  uint32_t class_code;

  struct nfos_pci_resource resources[PCI_NUM_RESOURCES];

  int interrupts_fd;
};

extern struct nfos_pci_nic *nfos_pci_find_nics(int *n);

#endif
