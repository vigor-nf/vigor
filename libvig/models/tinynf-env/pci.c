#include "env/pci.h"
#include "libvig/models/hardware.h"

uint32_t tn_pci_read(struct tn_pci_address address, uint8_t reg)
{
	if (reg == 0xAAu) {
		// DEVICESTATUS
		return 0;
	}
	if (reg == 0x44u) {
		// PMCSR
		return 0;
	}
	if (reg == 0x00u) {
		// ID
		return ((0x10FBu << 16) | 0x8086u);
	}
	if (reg == 0x10u) {
		// BAR0_LOW
		return ((uintptr_t) DEVICES[address.function].mem & 0xFFFFFFFF) | 0b100;
	}
	if (reg == 0x14u) {
		// BAR0_HIGH
		return ((uintptr_t) DEVICES[address.function].mem >> 32) & 0xFFFFFFFF;
	}
	// unknown
	return (uint32_t) -1;
}

void tn_pci_write(struct tn_pci_address address, uint8_t reg, uint32_t value)
{
	// OK, whatever
	// TODO check proper writes
}
