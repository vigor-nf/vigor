#ifndef _RTE_BYTEORDER_H_INCLUDED_
#define _RTE_BYTEORDER_H_INCLUDED_

#include <inttypes.h>

// This file MUST mirror exactly the way dpdk does it, including making the ANDs
// uint16 constants

static inline uint16_t rte_cpu_to_be_16(uint16_t x) {
  return ((x & UINT16_C(0x00FF)) << 8) | ((x & UINT16_C(0xFF00)) >> 8);
}

static inline uint16_t rte_be_to_cpu_16(uint16_t x) {
  return ((x & UINT16_C(0x00FF)) << 8) | ((x & UINT16_C(0xFF00)) >> 8);
}

#endif //_RTE_BYTEORDER_H_INCLUDED_
