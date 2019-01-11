#ifndef DSOS_PCI_H
#define DSOS_PCI_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define PCI_NUM_RESOURCES 6

struct dsos_pci_resource {
	void *start;
	size_t size;
	bool is_mem;
};

struct dsos_pci_nic {
	uint16_t vendor_id;
	uint16_t device_id;

	uint16_t subsystem_id;
	uint16_t subsystem_vendor_id;

	uint32_t class_code;

	struct dsos_pci_resource resources[PCI_NUM_RESOURCES];

	int interrupts_fd;
};

extern struct dsos_pci_nic *dsos_pci_find_nics(int *n);
extern void dsos_pci_print_nic_info(struct dsos_pci_nic *nic);

#endif
