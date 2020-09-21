// used with VeriFast, no pragma
#ifndef RTE_IP_H
#define RTE_IP_H

#include <stdint.h>

#define RTE_IPV4_HDR_IHL_MASK 0x0F
#define RTE_IPV4_IHL_MULTIXPLIER 4

#define PKT_TX_TCP_SEG (1ULL << 50)

struct rte_ipv4_hdr {
  uint8_t version_ihl;
  uint8_t type_of_service;
  uint16_t total_length;
  uint16_t packet_id;
  uint16_t fragment_offset;
  uint8_t time_to_live;
  uint8_t next_proto_id;
  uint16_t hdr_checksum;
  uint32_t src_addr;
  uint32_t dst_addr;
};
#endif
