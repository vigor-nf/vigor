#pragma once

#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>

#include <rte_ether.h>

bool nf_parse_etheraddr(const char* str, struct rte_ether_addr* addr)
{
  return sscanf(str, "%02hhX:%02hhX:%02hhX:%02hhX:%02hhX:%02hhX",
                addr->addr_bytes + 0,
                addr->addr_bytes + 1,
                addr->addr_bytes + 2,
                addr->addr_bytes + 3,
                addr->addr_bytes + 4,
                addr->addr_bytes + 5)
         == 6;
}

bool nf_parse_ipv4addr(const char* str, uint32_t* addr)
{
  uint8_t a, b, c, d;
  if (sscanf(str, "%hhu.%hhu.%hhu.%hhu", &a, &b, &c, &d) == 4) {
    *addr = ((uint32_t) a << 24) |
            ((uint32_t) b << 16) |
            ((uint32_t) c <<  8) |
            ((uint32_t) d <<  0);
    return true;
  }
  return false;
}
