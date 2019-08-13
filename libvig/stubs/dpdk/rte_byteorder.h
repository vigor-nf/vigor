#ifndef _RTE_BYTEORDER_H_INCLUDED_
#define _RTE_BYTEORDER_H_INCLUDED_

#include <stdint.h>

// This file MUST mirror exactly the way dpdk does it

static inline uint16_t
rte_cpu_to_be_16(uint16_t x)
{
	return ((x & 0x00FFu) << 8) | ((x & 0xFF00u) >> 8);
}

static inline uint16_t
rte_be_to_cpu_16(uint16_t x)
{
	return ((x & 0x00FFu) << 8) | ((x & 0xFF00u) >> 8);
}

#endif//_RTE_BYTEORDER_H_INCLUDED_
