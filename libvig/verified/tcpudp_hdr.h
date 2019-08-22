#ifndef _TCPUDP_H_INCLUDED_
#define _TCPUDP_H_INCLUDED_

#include <stdint.h>

struct tcpudp_hdr {
  uint16_t src_port;
  uint16_t dst_port;
}
#ifdef _NO_VERIFAST_
__attribute__((__packed__)) // VeriFast does not understand attributes
#endif                      //_NO_VERIFAST_
;

#endif //_TCPUDP_H_INCLUDED_
