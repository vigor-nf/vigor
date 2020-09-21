#ifndef _STAT_KEY_H_INCLUDED_
#define _STAT_KEY_H_INCLUDED_

#include <stdint.h>
#include <rte_ether.h>

struct StaticKey {
  struct rte_ether_addr addr;
  uint16_t device;
};

#endif //_STAT_KEY_H_INCLUDED_
