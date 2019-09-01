#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include "nfos_pci.h"
#include "nfos_portio.h"
#include "nfos_vga.h"
#include "nfos_serial.h"

#define MAX_PCI_DEVICES UINT32_C(32)

#define PCI_CONFIG_ADDRESS_PORT UINT16_C(0xcf8)
#define PCI_CONFIG_DATA_PORT UINT16_C(0xcfc)

#define PCI_NUM_BUSES UINT32_C(256)
#define PCI_DEVICES_PER_BUS UINT32_C(32)
#define PCI_FUNCTIONS_PER_DEVICE UINT32_C(8)

#define PCI_BAR_BASE UINT32_C(4)
#define PCI_INVALID_VENDOR_ID UINT16_C(0xFFFF)

#define PCI_VENDOR_REGISTER UINT32_C(0)
#define PCI_STATUS_COMMAND_REGISTER UINT32_C(1)
#define PCI_CLASS_CODE_REGISTER UINT32_C(2)
#define PCI_SUBSYSTEM_REGISTER UINT32_C(11)

#define PCI_COMMAND_MASTER UINT32_C(4)

/*
 * Taken from OpenBSD's reallocarray.c
 *
 * This is sqrt(SIZE_MAX+1), as s1*s2 <= SIZE_MAX
 * if both s1 < MUL_NO_OVERFLOW and s2 < MUL_NO_OVERFLOW
 *
 * The purpose of this is macro is to check that a multiplication between two
 * operands of type size_t will not overflow.
 */
#define MUL_NO_OVERFLOW (((size_t)1) << (sizeof(size_t) * 4))

/*
 * A PCI configuration register is read by sending a 32-bit address to I/O port
 * 0xCF8 (CONFIG_ADDRESS) and subsequently reading the 32-bit value from I/O
 * port 0xCFC (CONFIG_DATA).
 *
 * The 31st bit of the address must be set to initiate a bus configuration
 * transaction
 * Bits 30 to 24 are reserved and read-only, set to 0 in this function
 * Bits 23 to 16 choose a PCI bus on the system
 * Bits 15 to 11 choose a PCI device on the bus
 * Bits 10 to 8 choose a function in a device
 * Bits 7 to 2 choose a register in the device's configuration space.
 * Bits 1 and 0 must be 0.
 *
 * Writes to a non-existent device are silently dropped, reads from a
 * non-existent device return all 1s.
 */
static uint32_t nfos_read_pci_reg(uint32_t bus, uint32_t dev, uint32_t function,
                                  uint32_t reg) {
  assert(bus < PCI_NUM_BUSES);
  assert(dev < PCI_DEVICES_PER_BUS);
  assert(function < PCI_FUNCTIONS_PER_DEVICE);

  uint32_t addr = (bus << 16) | (dev << 11) | (function << 8) | (reg * 4) |
                  (UINT32_C(1) << 31);

  nfos_outl(addr, PCI_CONFIG_ADDRESS_PORT);
  return nfos_inl(PCI_CONFIG_DATA_PORT);
}

/*
 * In order to write to a configuration register the CPU must write the address
 * to CONFIG_ADDRESS, and subsequently write the data to CONFIG_DATA.
 */
static void nfos_write_pci_reg(uint32_t bus, uint32_t dev, uint32_t function,
                               uint32_t reg, uint32_t val) {
  assert(bus < PCI_NUM_BUSES);
  assert(dev < PCI_DEVICES_PER_BUS);
  assert(function < PCI_FUNCTIONS_PER_DEVICE);

  uint32_t addr = (bus << 16) | (dev << 11) | (function << 8) | (reg * 4) |
                  (UINT32_C(1) << 31);

  nfos_outl(addr, PCI_CONFIG_ADDRESS_PORT);
  nfos_outl(val, PCI_CONFIG_DATA_PORT);
}

/*
 * In order to read a BAR we have to write all 1s to the address register then
 * read it back and check how many LSBs are clear (after masking out the lowest
 * 2 or 4 because those are not part of the address). The region size is 2 **
 * the number of clear bits. We also need to restore the original value of the
 * register afterwards.
 *
 * See
 * https://stackoverflow.com/questions/19006632/how-is-a-pci-pcie-bar-size-determined/39618552#39618552
 */
static void nfos_pci_read_resource(uint32_t bus, uint32_t dev,
                                   uint32_t function, uint32_t index,
                                   struct nfos_pci_resource *out) {
  uint32_t reg = index + PCI_BAR_BASE;
  uint32_t orig_value = nfos_read_pci_reg(bus, dev, function, reg);

  nfos_write_pci_reg(bus, dev, function, reg, 0xFFFFFFFFul);

  uint32_t read_value = nfos_read_pci_reg(bus, dev, function, reg);

  /* Restore the original value */
  nfos_write_pci_reg(bus, dev, function, reg, orig_value);

  if ((orig_value & 1) == 0) {
    /* Memory mapped resource, ignore the lowest 4 bits */
    out->start = (void *)(uintptr_t)(orig_value & 0xFFFFFFF0ul);
    out->size = (size_t)(uint32_t)((~(read_value & 0xFFFFFFF0ul)) + 1);
    out->is_mem = true;

  } else {
    /* I/O mapped resource, ignore the lowest 2 bits */
    out->start = (void *)(uintptr_t)(orig_value & 0xFFFFFFFCul);
    out->size = (size_t)(uint32_t)((~(read_value & 0xFFFFFFFCul)) + 1);
    out->is_mem = false;
  }
}

/*
 * Probes the specified PCI device on the specified bus to check if it exists.
 * If it does, returns 1 and fills the data structure with data read from the
 * device, otherwise returns 0. We assume that each device is uniquely
 * identified by the (bus, device) pair. The function assumes that out points to
 * valid memory. We also assume that each PCI device has only one function.
 */
static int nfos_pci_probe_dev(uint32_t bus, uint32_t dev, uint32_t function,
                              struct nfos_pci_nic *out) {
  /*
   * Each PCI device provides 256 bytes of configuration registers that can
   * be read and written to by the CPU. Each register is 32-bit wide.
   *
   * The register at offset 0 contains the device ID in the upper 16 bits and
   * the vendor ID in the bottom 16 bits. These two numbers uniquely identify
   * a vendor and device type and are used by DPDK drivers to recognize
   * supported devices.
   */
  uint32_t vendor_reg =
      nfos_read_pci_reg(bus, dev, function, PCI_VENDOR_REGISTER);
  uint16_t vendor_id = (uint16_t)(vendor_reg & 0xFFFF);
  uint16_t device_id = (uint16_t)(vendor_reg >> 16);

  /*
   * 0xFFFF is an invalid vendor ID that will be returned when the Vendor ID
   * is read for a non-existing device. Therefore when this value is read the
   * device should be skipped. The function returns 0 because it didn't find
   * any device for this combination of (bus, dev)
   */
  if (vendor_id == PCI_INVALID_VENDOR_ID) {
    return 0;
  }

  /* Ignore non-IXGBE */
  if (vendor_id != 0x8086 || device_id != 0x10fb) {
    return 0;
  }

  /*
   * We assume that out points to valid memory. Because PCI devices are
   * always little-endian, it is not necessary to perform byte-swapping.
   */
  out->vendor_id = vendor_id;
  out->device_id = device_id;

  /*
   * Configuration register 11 contains the subsystem ID in the upper 16 bits
   * and the subsystem vendor ID in the lower 16 bits.
   */
  uint32_t subsystem_reg =
      nfos_read_pci_reg(bus, dev, function, PCI_SUBSYSTEM_REGISTER);
  out->subsystem_id = (uint16_t)(subsystem_reg >> 16);
  out->subsystem_vendor_id = (uint16_t)(subsystem_reg & 0xFFFF);

  /*
   * Rgister 2 contains the device's class code (the type of function that the
   * device performs) in the top 8 bits.
   */
  uint32_t class_code_reg =
      nfos_read_pci_reg(bus, dev, function, PCI_CLASS_CODE_REGISTER);
  out->class_code = class_code_reg >> 24;

  /*
   * Each device has 6 base address registers (BARs) that hold addresses
   * belonging to the device. These addresses can be either in memory or in
   * port I/O space. We read the base address, type and size of each BAR into
   * out.
   */
  for (uint32_t i = 0; i < (sizeof(out->resources) / sizeof(out->resources[0]));
       i++) {
    nfos_pci_read_resource(bus, dev, function, i, &(out->resources[i]));
  }

  /*
   * We need to enable bus mastering for each device so that they are able
   * to initiate DMA transfers. This is requried for IXGBE to function properly.
   * Enabling bus mastering for a device is done by setting bit 2 in the command
   * register (register 0x4).
   */
  uint32_t status_command_reg =
      nfos_read_pci_reg(bus, dev, function, PCI_STATUS_COMMAND_REGISTER);
  status_command_reg |= PCI_COMMAND_MASTER;
  nfos_write_pci_reg(bus, dev, function, PCI_STATUS_COMMAND_REGISTER,
                     status_command_reg);

  // Return 1 because a device was found.
  return 1;
}

/*
 * Find all PCI devices (up to MAX_PCI_DEVICES) and read some information that
 * DPDK needs from these devices.
 * This function will either return a pointer to the start of an array of
 * struct nfos_pci_nic or trigger an assertion failure. The int pointed to by n
 * will be set to the number of valid entries in the array.
 * Each element of the array will contain information about a PCI device on the
 * system. PCI bus mastering will be enabled for every device on the system.
 *
 * We assume that there are no PCI bridges in the system, and therefore
 * recursive enumeration of the PCI bus is not needed.
 */
struct nfos_pci_nic *nfos_pci_find_nics(int *n) {
  // Assert that the product will not overwlow
  static_assert(MAX_PCI_DEVICES < MUL_NO_OVERFLOW,
                "MAX_PCI_DEVICES is too large");
  static_assert(sizeof(struct nfos_pci_nic) < MUL_NO_OVERFLOW,
                "nfos_pci_nic is too large");

  // malloc() can either return NULL or a pointer to valid memory
  struct nfos_pci_nic *devs =
      malloc(MAX_PCI_DEVICES * sizeof(struct nfos_pci_nic));
  assert(devs != NULL);

  // We have already proven that MAX_PCI_DEVICES doesn't overflow and
  // malloc has returned enough valid memory
  memset(devs, 0, MAX_PCI_DEVICES * sizeof(struct nfos_pci_nic));

  // Ensure that the counters cannot overflow
  static_assert(MAX_PCI_DEVICES < UINT32_MAX, "MAX_PCI_DEVICES is too large");

  // Because both operands are less than the square root of the maximum value
  // of uint32_t the multiplication between them cannot overflow
  static_assert(PCI_NUM_BUSES < UINT16_MAX, "PCI_NUM_BUSES is too large");
  static_assert(PCI_DEVICES_PER_BUS < UINT16_MAX,
                "PCI_DEVICES_PER_BUS is too large");

  // Ensure that we don't divide by 0
  static_assert(PCI_DEVICES_PER_BUS != 0, "PCI_DEVICES_PER_BUS is zero");

  // This loop executes for a fixed number of iterations, therefore it always
  // terminates

  int num_devices = 0;
  for (uint32_t i = 0;
       i < PCI_NUM_BUSES * PCI_DEVICES_PER_BUS * PCI_FUNCTIONS_PER_DEVICE;
       i++) {
    // Division and modulo by the same number creates a one-to-one mapping
    // between i and (bus, current_dev)
    uint32_t function = i % PCI_FUNCTIONS_PER_DEVICE;
    uint32_t device = (i / PCI_FUNCTIONS_PER_DEVICE) % PCI_DEVICES_PER_BUS;
    uint32_t bus = (i / PCI_FUNCTIONS_PER_DEVICE) / PCI_DEVICES_PER_BUS;

    /*
     * Loop invariant: num_devices is equal to the number of devices that
     * have been found on the PCI bus so far, up to a maximum of
     * MAX_PCI_DEVICES.
     * Because num_devices can only be incremented if it is less than
     * MAX_PCI_DEVICES, and it can only be incremented by 1, it can never be
     * greater than MAX_PCI_DEVICES.
     *
     * Loop invariant: devs[0..num_devices] is valid and each entry is
     * filled in with information about a different PCI device. Whenever a
     * new PCI device is found, nfos_pci_probe_dev returns a non-zero result
     * and writes the information of the new device in devs[num_devices],
     * then num_devices is incremented. num_devices is not incremented under
     * any other circumstances. The value of (bus, device) never
     * repeats more than once, so each device is only scanned once
     */

    if (num_devices < MAX_PCI_DEVICES) {
      // Because each (bus, device) pair occurs only once, each
      // PCI device is only probed once
      if (nfos_pci_probe_dev(bus, device, function, &devs[num_devices]) != 0) {
        // A device was found
        num_devices++;
      }
    }
  }

  /*
   * num_devices is equal to the number of devices that were found by scanning
   * the PCI bus, and so is *n.
   */
  *n = num_devices;
  return devs;
}
