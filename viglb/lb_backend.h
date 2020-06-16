#ifndef _LB_BACKEND_H_INCLUDED_
#define _LB_BACKEND_H_INCLUDED_

#include <stdint.h>
#include <rte_ether.h>

struct LoadBalancedBackend {
  uint16_t nic;
  struct rte_ether_addr mac;
  uint32_t ip;
};

#endif //_LB_BACKEND_H_INCLUDED_
