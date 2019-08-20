#ifndef _LB_FLOW_H_INCLUDED_
#define _LB_FLOW_H_INCLUDED_

#include <stdint.h>

struct LoadBalancedFlow {
  uint32_t src_ip;
  uint32_t dst_ip;
  uint16_t src_port;
  uint16_t dst_port;
  uint8_t protocol;
};

#endif //_LB_FLOW_H_INCLUDED_
