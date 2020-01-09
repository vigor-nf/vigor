#include "nat_config.h"
#include "nf.h"
#include "nf-util.h"

struct nf_config config;

bool nf_init(void) {
  return true;
}

int nf_process(uint16_t device, uint8_t* buffer, uint16_t buffer_length, time_t now) {
  // Mark now as unused, we don't care about time
  (void)now;

#ifdef VIGOR_DEBUG_REALNOP
  // "Real" no-op, i.e. do absolutely nothing, this is unrealistic but useful
  // to measure performance of the overall Vigor architecture
  return 1 - device;
#else
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
  struct ether_hdr *ether_header = nf_then_get_ether_header(buffer);
  ether_header->s_addr = config.device_macs[dst_device];
  ether_header->d_addr = config.endpoint_macs[dst_device];

  return dst_device;
#endif
}
