#ifndef RTE_ETHER_H
#define RTE_ETHER_H

#include <stddef.h>
#include <stdint.h>

#define RTE_ETHER_TYPE_IPV4 0x0800
#define RTE_ETHER_MAX_LEN 1518

struct rte_ether_addr {
  uint8_t addr_bytes[6];
};

struct rte_ether_hdr {
  struct rte_ether_addr d_addr;
  struct rte_ether_addr s_addr;
  uint16_t ether_type;
};

#endif // RTE_ETHER_H
