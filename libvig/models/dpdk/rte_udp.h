#pragma once

struct rte_udp_hdr {
  uint16_t src_port;
  uint16_t dst_port;
  uint16_t dgram_len;
  uint16_t dgram_cksum;
};
