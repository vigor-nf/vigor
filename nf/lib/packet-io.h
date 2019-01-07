#ifndef _PACKET_IO_H_INCLUDED_
#define  _PACKET_IO_H_INCLUDED_

#include <rte_byteorder.h>
#include <rte_common.h>
#include <rte_ether.h>
#include <rte_ip.h>
#include <rte_mbuf.h>
#include <rte_mbuf_ptype.h>

#include "lib/nf_util.h"

struct Packet {
  struct rte_mbuf* mbuf;

  //Warning: uninitialized at first. gets initialized by packet_get_ipv4_header.
  struct ipv4_hdr* h;
};

static inline
struct ether_hdr* packet_get_ether_header(struct Packet* p) {
  p->h = NULL;
  return nf_get_mbuf_ether_header(p->mbuf);
}

static inline
struct ipv4_hdr* packet_then_get_ipv4_header(struct Packet* p) {
  p->h = nf_get_mbuf_ipv4_header(p->mbuf);
  return p->h;
}

static inline
struct tcpudp_hdr* packet_then_get_tcpudp_header(struct Packet* p) {
  return nf_get_ipv4_tcpudp_header(p->h);
}

static inline
void packet_set_ip_ip_checksum(struct Packet* p) {
  //Don't do that for now: avoid messing with symbex and validator
  //TODO
  // hardware offload??
}

static inline
uint16_t packet_get_port(struct Packet* p) {
  return p->mbuf->port;
}

#endif// _PACKET_IO_H_INCLUDED_
