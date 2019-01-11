#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <assert.h>

#include "lib/packet-io.h"
#include "rte_ip.h"

// rte_ether
struct ether_addr;
struct ether_hdr;

// rte_ip
struct ipv4_hdr;

#define IP_MIN_SIZE_WORDS 5
#define WORD_SIZE 4


// A header for TCP or UDP packets, containing common data.
// (This is used to point into DPDK data structures!)
struct tcpudp_hdr {
	uint16_t src_port;
	uint16_t dst_port;
} __attribute__((__packed__));


bool nf_has_tcpudp_header(struct ipv4_hdr* header);

void nf_set_ipv4_checksum(struct ipv4_hdr* header);

uintmax_t nf_util_parse_int(const char* str, const char* name,
                            int base, char next);

char* nf_mac_to_str(struct ether_addr* addr);

char* nf_ipv4_to_str(uint32_t addr);

#define MAX_N_CHUNKS 100
extern uint8_t* chunks_borrowed[];
extern size_t chunks_borrowed_num;

static inline
uint8_t* nf_borrow_next_chunk(struct Packet* p, size_t length) {
  assert(chunks_borrowed_num < MAX_N_CHUNKS);
  uint8_t* chunk;
  packet_borrow_next_chunk(p, length, &chunk);
  chunks_borrowed[chunks_borrowed_num] = chunk;
  chunks_borrowed_num++;
  return chunk;
}

static inline
void nf_return_all_chunks(struct Packet* p) {
  do {
    chunks_borrowed_num--;
    packet_return_chunk(p, chunks_borrowed[chunks_borrowed_num]);
  } while(chunks_borrowed_num != 0);
}

static inline
struct ether_hdr* nf_then_get_ether_header(struct Packet* p) {
  void* hdr = nf_borrow_next_chunk(p, sizeof(struct ether_hdr));
  return (struct ether_hdr*)hdr;
}

static inline
struct ipv4_hdr* nf_then_get_ipv4_header(struct Packet* p, uint8_t** ip_options,
                                         bool* wellformed) {
  assert(packet_is_ipv4(p));
  if (packet_get_unread_length(p) < sizeof(struct ipv4_hdr)) {
    *ip_options = NULL;
    *wellformed = false;
    return NULL;
  }
  struct ipv4_hdr* hdr = (struct ipv4_hdr*)nf_borrow_next_chunk(p, sizeof(struct ipv4_hdr));
  uint8_t ihl = hdr->version_ihl & 0x0f;
  if (ihl < IP_MIN_SIZE_WORDS) { //Malformed ipv4 packet
    *ip_options = NULL;
    *wellformed = false;
    return hdr;
  }
  *wellformed = true;
  uint16_t ip_options_length = (ihl - IP_MIN_SIZE_WORDS) * WORD_SIZE;
  if (ip_options_length != 0) {
    if (packet_get_unread_length(p) < ip_options_length) {
      *ip_options = NULL;
      *wellformed = false;
    } else {
      *ip_options = nf_borrow_next_chunk(p, ip_options_length);
    }
  }
  return hdr;
}

static inline
struct tcpudp_hdr* nf_then_get_tcpudp_header(struct Packet* p) {
  return (struct tcpudp_hdr*)nf_borrow_next_chunk(p, sizeof(struct tcpudp_hdr));
}


