#ifndef _PACKET_IO_H_INCLUDED_
#define  _PACKET_IO_H_INCLUDED_

#include <inttypes.h>
#include <assert.h>
#include <rte_byteorder.h>
#include <rte_common.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_ip.h>
#include <rte_mbuf.h>
#include <rte_mbuf_ptype.h>

#include "lib/nf_util.h"

#define IP_MIN_SIZE_WORDS 5
#define WORD_SIZE 4

struct Packet {
  struct rte_mbuf* mbuf;
  char* unread_buf;
};

// The main IO primitive.
char* packet_borrow_next_chunk(struct Packet* p, size_t length);
void packet_return_all_chunks(struct Packet* p);
bool packet_receive(struct Packet* p, uint16_t src_device);
void packet_send(struct Packet* p, uint16_t dst_device);
// Flood method for the bridge
void packet_flood(struct Packet* p, uint16_t skip_device, uint16_t nb_devices);
void packet_free(struct Packet* p);

static inline
struct ether_hdr* packet_then_get_ether_header(struct Packet* p) {
  void* hdr = packet_borrow_next_chunk(p, sizeof(struct ether_hdr));
  return (struct ether_hdr*)hdr;
}

static inline
bool packet_is_ipv4(struct Packet* p) {
  return RTE_ETH_IS_IPV4_HDR(p->mbuf->packet_type);
}

static inline
struct ipv4_hdr* packet_then_get_ipv4_header(struct Packet* p, char** ip_options) {
  assert(packet_is_ipv4(p));
  struct ipv4_hdr* hdr = (struct ipv4_hdr*)packet_borrow_next_chunk(p, sizeof(struct ipv4_hdr));
  uint8_t ihl = hdr->version_ihl & 0x0f;
  assert(IP_MIN_SIZE_WORDS <= ihl);
  uint16_t ip_options_length = (ihl - IP_MIN_SIZE_WORDS) * WORD_SIZE;
  if (ip_options_length != 0)
    *ip_options = packet_borrow_next_chunk(p, ip_options_length);
  return hdr;
}

static inline
struct tcpudp_hdr* packet_then_get_tcpudp_header(struct Packet* p) {
  return (struct tcpudp_hdr*)packet_borrow_next_chunk(p, sizeof(struct tcpudp_hdr));
}

static inline
uint16_t packet_get_port(struct Packet* p) {
  return p->mbuf->port;
}

#endif// _PACKET_IO_H_INCLUDED_
