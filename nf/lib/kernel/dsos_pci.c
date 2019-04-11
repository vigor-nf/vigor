#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include "dsos_pci.h"
#include "dsos_portio.h"
#include "dsos_vga.h"

static const unsigned int MAX_PCI_DEVICES = 32;

static const uint16_t PCI_ADDR_PORT = 0xcf8;
static const uint16_t PCI_DATA_PORT = 0xcfc;

static const uint32_t PCI_NUM_BUSES = 256;
static const uint32_t PCI_DEVICES_PER_BUS = 32;

static const uint32_t PCI_BAR_BASE = 4;
static const uint16_t PCI_INVALID_VENDOR_ID = 0xFFFF;

static const uint32_t PCI_VENDOR_REGISTER = 0;
static const uint32_t PCI_CLASS_CODE_REGISTER = 2;
static const uint32_t PCI_SUBSYSTEM_REGISTER = 11;

/* Read a PCI configuration register */
static uint32_t dsos_read_pci_reg(uint32_t bus, uint32_t dev, uint32_t function, uint32_t reg)
{
	uint32_t addr = (bus << 16) | (dev << 11) | (function << 8) |
		(reg * 4) | 0x80000000ul;

	dsos_outl(addr, PCI_ADDR_PORT);
	return dsos_inl(PCI_DATA_PORT);
}

/* Write a PCI configuration register */
static void dsos_write_pci_reg(uint32_t bus, uint32_t dev, uint32_t function, uint32_t reg, uint32_t val)
{
	uint32_t addr = (bus << 16) | (dev << 11) | (function << 8) |
		(reg * 4) | 0x80000000ul;

	dsos_outl(addr, PCI_ADDR_PORT);
	dsos_outl(val, PCI_DATA_PORT);
}

/*
 * This reads the size of a memory/IO mapped resource in a convoluted way
 * because PCI. We have to write all 1s to the address register then read it back
 * and check how many LSBs are clear (after masking out the lowest 2 or 4 because
 * those are not part of the address). The region size is 2 ** the number of
 * clear bits. We also need to restore the original value of the register afterwards.
 *
 * See https://stackoverflow.com/questions/19006632/how-is-a-pci-pcie-bar-size-determined/39618552#39618552
 */
static void dsos_pci_read_resource(uint32_t bus, uint32_t dev, uint32_t function, uint32_t index, struct dsos_pci_resource *out)
{
	uint32_t reg = index + PCI_BAR_BASE;
	uint32_t orig_value = dsos_read_pci_reg(bus, dev, function, reg);

	dsos_write_pci_reg(bus, dev, function, reg, 0xFFFFFFFFul);

	uint32_t read_value = dsos_read_pci_reg(bus, dev, function, reg);

	/* Restore the original value */
	dsos_write_pci_reg(bus, dev, function, reg, orig_value);

	if ((orig_value & 1) == 0) {
		/* Memory mapped resource, ignore the lowest 4 bits */
		out->start = (void *)(orig_value & 0xFFFFFFF0ul);
		out->size = (size_t)((~(read_value & 0xFFFFFFF0ul)) + 1);
		out->is_mem = true;
	} else {
		/* I/O mapped resource, ignore the lowest 2 bits */
		out->start = (void *)(orig_value & 0xFFFFFFFCul);
		out->size = (size_t)((~(read_value & 0xFFFFFFFCul)) + 1);
		out->is_mem = false;
	}
}

/*
 * Probes a PCI device to check if it exists. If it does, returns 1 and fills
 * the data structure, otherwise returns 0.
 */
static int dsos_pci_probe_dev(uint32_t bus, uint32_t dev, struct dsos_pci_nic *out)
{
	uint32_t vendor_reg = dsos_read_pci_reg(bus, dev, 0, PCI_VENDOR_REGISTER);
	uint16_t vendor_id = (uint16_t)(vendor_reg & 0xFFFF);
	uint16_t device_id = (uint16_t)(vendor_reg >> 16);

	/* Invalid vendor = device does not exist */
	if (vendor_id == PCI_INVALID_VENDOR_ID) {
		return 0;
	}

	out->vendor_id = vendor_id;
	out->device_id = device_id;

	/* TODO: enumerate bridges recursively */

	uint32_t subsystem_reg = dsos_read_pci_reg(bus, dev, 0, PCI_SUBSYSTEM_REGISTER);
	out->subsystem_id = (uint16_t)(subsystem_reg >> 16);
	out->subsystem_vendor_id = (uint16_t)(subsystem_reg & 0xFFFF);

	uint32_t class_code_reg = dsos_read_pci_reg(bus, dev, 0, PCI_CLASS_CODE_REGISTER);
	out->class_code = class_code_reg >> 24;

	for (uint32_t i = 0; i < PCI_NUM_RESOURCES; i++) {
		dsos_pci_read_resource(bus, dev, 0, i, &(out->resources[i]));
	}

	return 1;
}

/*
 * Find all PCI devices (up to MAX_PCI_DEVICES) and read some information that
 * DPDK needs.
 */

struct dsos_pci_nic *dsos_pci_find_nics(int *n)
{
	struct dsos_pci_nic *devs;

	devs = malloc(MAX_PCI_DEVICES * sizeof(struct dsos_pci_nic));
	if (devs == NULL) {
		return NULL;
	}

	memset(devs, 0, MAX_PCI_DEVICES * sizeof(struct dsos_pci_nic));

	int num_devices = 0;
	uint32_t current_dev = 0;
	uint32_t current_bus = 0;

	while (num_devices < MAX_PCI_DEVICES) {
		struct dsos_pci_nic *p;

		int ret = dsos_pci_probe_dev(current_bus, current_dev, &devs[num_devices]);

		if (ret != 0) {
			/* A device was found */
			num_devices++;
		}

		current_dev++;

		if (current_dev >= PCI_DEVICES_PER_BUS) {
			/* We have probed all the devices on this bus, move on to the next */
			current_bus++;
			current_dev = 0;
		}

		if (current_bus >= PCI_NUM_BUSES) {
			/* We have probed all devices on all buses, exit */
			break;
		}
	}

	*n = num_devices;
	return devs;
}

void dsos_pci_print_nic_info(struct dsos_pci_nic *nic)
{
	dsos_vga_write_str("Vendor ID: ");
	dsos_vga_write_int(nic->vendor_id);

	dsos_vga_write_str("\nDevice ID: ");
	dsos_vga_write_int(nic->device_id);

	dsos_vga_write_str("\nSubsystem ID: ");
	dsos_vga_write_int(nic->subsystem_id);

	dsos_vga_write_str("\nSubsystem vendor ID: ");
	dsos_vga_write_int(nic->subsystem_vendor_id);

	dsos_vga_write_str("\nClass code: ");
	dsos_vga_write_int(nic->class_code);

	dsos_vga_write_char('\n');
}
