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

int nf_process(uint16_t device, uint8_t* buffer, uint16_t packet_length, vigor_time_t now) {
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

  struct rte_ether_hdr *rte_ether_header = nf_then_get_rte_ether_header(buffer);
  uint8_t *ip_options;
  struct rte_ipv4_hdr *rte_ipv4_header =
      nf_then_get_rte_ipv4_header(rte_ether_header, buffer, &ip_options);
  if (rte_ipv4_header == NULL) {
    NF_DEBUG("Not IPv4, dropping");
    return device;
  }

  struct tcpudp_hdr *tcpudp_header =
      nf_then_get_tcpudp_header(rte_ipv4_header, buffer);
  if (tcpudp_header == NULL) {
    NF_DEBUG("Not TCP/UDP, dropping");
    return device;
  }
  // You could do something with the headers here...
  // ...which would probably require you to recompute the checksums
  nf_set_rte_ipv4_udptcp_checksum(rte_ipv4_header, tcpudp_header, buffer);

  uint16_t dst_device = 1 - device;

  // Special method required during symbolic execution to avoid path explosion
  concretize_devices(&dst_device, rte_eth_dev_count_avail);

  rte_ether_header->s_addr = config.device_macs[dst_device];
  rte_ether_header->d_addr = config.endpoint_macs[dst_device];

  return dst_device;
}
