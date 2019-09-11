#include "nf.h"
#include "config.h"

#include "nf-log.h"
#include "nf-util.h"

// ===
// Include the state, and the generated structures, like so:
// ===
#include "state.h"
#include "flow.h.gen.h"

// ===
// Define the config, which is only an extern in nf.h, like so:
// ===
struct nf_config config;

bool nf_init(void) {
  // ===
  // Initialize your NF here, e.g. non-configuration global variables
  // You must at least allocate the state.
  // ===
  return alloc_state(42) != NULL;
}

int nf_process(uint16_t device, uint8_t* buffer, uint16_t buffer_length, vigor_time_t now) {
  // ===
  // Process the packet here, and return either the device on which the packet
  // should be forwarded, or:
  // - the input device, to drop the packet, or
  // - FLOOD_FRAME, to send the packet to all devices except the input one.
  //
  // You can access the configuration using the 'config' global variable, as
  // declared in nf.h.
  //
  // This example simply reads the L2/L3/L4 headers, changes the L2 addresses,
  // then forwards to the "other" device, assuming there are 2.
  // ===

  struct ether_hdr *ether_header = nf_then_get_ether_header(buffer);
  uint8_t *ip_options;
  struct ipv4_hdr *ipv4_header =
      nf_then_get_ipv4_header(ether_header, buffer, &ip_options);
  if (ipv4_header == NULL) {
    NF_DEBUG("Not IPv4, dropping");
    return device;
  }

  struct tcpudp_hdr *tcpudp_header =
      nf_then_get_tcpudp_header(ipv4_header, buffer);
  if (tcpudp_header == NULL) {
    NF_DEBUG("Not TCP/UDP, dropping");
    return device;
  }
  // You could do something with the headers here...
  // ...which would probably require you to recompute the checksums
  nf_set_ipv4_udptcp_checksum(ipv4_header, tcpudp_header, buffer);

  uint16_t dst_device = 1 - device;

  // Special method required during symbolic execution to avoid path explosion
  concretize_devices(&dst_device, rte_eth_dev_count());

  ether_header->s_addr = config.device_macs[dst_device];
  ether_header->d_addr = config.endpoint_macs[dst_device];

  return dst_device;
}
