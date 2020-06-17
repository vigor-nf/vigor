#include "nat_config.h"
#include "nf.h"
#include "nf-util.h"

struct nf_config config;

bool nf_init(void) {
  return true;
}

int nf_process(uint16_t device, uint8_t* buffer, uint16_t packet_length, vigor_time_t now) {
  // Mark now as unused, we don't care about time
  (void)now;

  // This is a bit of a hack; the benchmarks are designed for a NAT, which knows
  // where to forward packets, but for a plain forwarding app without any logic,
  // we just send all packets from LAN to the WAN port, and all packets from WAN
  // to the main LAN port, and let the recipient ignore the useless ones.

  uint16_t dst_device;
  if (device == config.wan_device) {
    dst_device = config.lan_main_device;
  } else {
    dst_device = config.wan_device;
  }

  // L2 forwarding
  struct rte_ether_hdr *rte_ether_header = nf_then_get_rte_ether_header(buffer);
  rte_ether_header->s_addr = config.device_macs[dst_device];
  rte_ether_header->d_addr = config.endpoint_macs[dst_device];

  return dst_device;
}
