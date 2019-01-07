#ifndef _PACKET_IO_H_INCLUDED_
#define  _PACKET_IO_H_INCLUDED_

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

static inline
void packet_init(struct Packet* p) {
  assert(p->mbuf != NULL);
  p->unread_buf = (char*)p->mbuf->buf_addr + p->mbuf->data_off;
}

// The main IO primitive.
static inline
char* packet_borrow_next_chunk(struct Packet* p, size_t length) {
  //TODO: check for overflowing the current mbuf.
  char* ret = p->unread_buf;
  p->unread_buf += length;
  return ret;
}

static inline
void packet_return_all_chunks(struct Packet* p) {
  //Do nothing. needed only for verification
}

static inline
bool packet_receive(struct Packet* p, uint16_t src_device) {
  struct rte_mbuf* buf = NULL;
  uint16_t actual_rx_len = rte_eth_rx_burst(src_device, 0, &buf, 1);

  if (actual_rx_len != 0) {
    p->mbuf = buf;
    packet_init(p);
    return true;
  } else {
    return false;
  }
}

static inline
void packet_send(struct Packet* p, uint16_t dst_device) {
  uint16_t actual_tx_len = rte_eth_tx_burst(dst_device, 0, &p->mbuf, 1);
  if (actual_tx_len == 0) {
    rte_pktmbuf_free(p->mbuf);
  }
}

// Flood method for the bridge
#ifdef KLEE_VERIFICATION
void packet_flood(struct Packet* p, uint16_t skip_device, uint16_t nb_devices); // defined in stubs
#else
extern struct rte_mempool* clone_pool;
static inline
void
packet_flood(struct Packet* p, uint16_t skip_device, uint16_t nb_devices) {
  struct rte_mbuf* frame = p->mbuf;
  for (uint16_t device = 0; device < nb_devices; device++) {
    if (device == skip_device) continue;
    struct rte_mbuf* copy = rte_pktmbuf_clone(frame, clone_pool);
    if (copy == NULL) {
      rte_exit(EXIT_FAILURE, "Cannot clone a frame for flooding");
    }
    uint16_t actual_tx_len = rte_eth_tx_burst(device, 0, &copy, 1);

    if (actual_tx_len == 0) {
      rte_pktmbuf_free(copy);
    }
  }
  rte_pktmbuf_free(frame);
}
#endif//!KLEE_VERIFICATION

static inline
void packet_free(struct Packet* p) {
  rte_pktmbuf_free(p->mbuf);
}


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
