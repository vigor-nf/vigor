#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <assert.h>

#include <rte_ether.h>
#include <rte_ip.h>
#include <rte_tcp.h>
#include <rte_udp.h>
#include "lib/packet-io.h"
#include "lib/tcpudp.h"

#ifdef KLEE_VERIFICATION
#include "lib/stubs/containers/str-descr.h"
#include "lib/stubs/packet-io-stub-control.h"
#endif//KLEE_VERIFICATION

// rte_ether
struct ether_addr;
struct ether_hdr;

// rte_ip
struct ipv4_hdr;

#define IP_MIN_SIZE_WORDS 5
#define WORD_SIZE 4


#ifdef KLEE_VERIFICATION
static struct str_field_descr ether_fields[] = {
  {offsetof(struct ether_hdr, ether_type), sizeof(uint16_t), 0, "ether_type"},
  {offsetof(struct ether_hdr, d_addr), sizeof(struct ether_addr), 0, "d_addr"},
  {offsetof(struct ether_hdr, s_addr), sizeof(struct ether_addr), 0, "s_addr"}
};
static struct str_field_descr ipv4_fields[] = {
  {offsetof(struct ipv4_hdr, version_ihl), sizeof(uint8_t), 0, "version_ihl"},
  {offsetof(struct ipv4_hdr, type_of_service), sizeof(uint8_t), 0, "type_of_service"},
  {offsetof(struct ipv4_hdr, total_length), sizeof(uint16_t), 0, "total_length"},
  {offsetof(struct ipv4_hdr, packet_id), sizeof(uint16_t), 0, "packet_id"},
  {offsetof(struct ipv4_hdr, fragment_offset), sizeof(uint16_t), 0, "fragment_offset"},
  {offsetof(struct ipv4_hdr, time_to_live), sizeof(uint8_t), 0, "time_to_live"},
  {offsetof(struct ipv4_hdr, next_proto_id), sizeof(uint8_t), 0, "next_proto_id"},
  {offsetof(struct ipv4_hdr, hdr_checksum), sizeof(uint16_t), 0, "hdr_checksum"},
  {offsetof(struct ipv4_hdr, src_addr), sizeof(uint32_t), 0, "src_addr"},
  {offsetof(struct ipv4_hdr, dst_addr), sizeof(uint32_t), 0, "dst_addr"}
};
static struct str_field_descr tcpudp_fields[] = {
  {offsetof(struct tcp_hdr, src_port), sizeof(uint16_t), 0, "src_port"},
  {offsetof(struct tcp_hdr, dst_port), sizeof(uint16_t), 0, "dst_port"}
};
static struct str_field_descr tcp_fields[] = {
  {offsetof(struct tcp_hdr, src_port), sizeof(uint16_t), 0, "src_port"},
  {offsetof(struct tcp_hdr, dst_port), sizeof(uint16_t), 0, "dst_port"},
  {offsetof(struct tcp_hdr, sent_seq), sizeof(uint32_t), 0, "sent_seq"},
  {offsetof(struct tcp_hdr, recv_ack), sizeof(uint32_t), 0, "recv_ack"},
  {offsetof(struct tcp_hdr, data_off), sizeof(uint8_t), 0, "data_off"},
  {offsetof(struct tcp_hdr, tcp_flags), sizeof(uint8_t), 0, "tcp_flags"},
  {offsetof(struct tcp_hdr, rx_win), sizeof(uint16_t), 0, "rx_win"},
  {offsetof(struct tcp_hdr, cksum), sizeof(uint16_t), 0, "cksum"},
  {offsetof(struct tcp_hdr, tcp_urp), sizeof(uint16_t), 0, "tcp_urp"}
};
static struct nested_field_descr ether_nested_fields[] = {
  {offsetof(struct ether_hdr, d_addr), 0, sizeof(uint8_t), 6, "addr_bytes"},
  {offsetof(struct ether_hdr, s_addr), 0, sizeof(uint8_t), 6, "addr_bytes"}
};
#endif//KLEE_VERIFICATION


bool nf_has_tcpudp_header(struct ipv4_hdr* header);

void nf_set_ipv4_checksum(struct ipv4_hdr* header);

uintmax_t nf_util_parse_int(const char* str, const char* name,
                            int base, char next);

char* nf_mac_to_str(struct ether_addr* addr);

char* nf_ipv4_to_str(uint32_t addr);

#define MAX_N_CHUNKS 100
extern void* chunks_borrowed[];
extern size_t chunks_borrowed_num;

static inline
void* nf_borrow_next_chunk(struct Packet* p, size_t length) {
  assert(chunks_borrowed_num < MAX_N_CHUNKS);
  void* chunk;
  packet_borrow_next_chunk(p, length, &chunk);
  chunks_borrowed[chunks_borrowed_num] = chunk;
  chunks_borrowed_num++;
  return chunk;
}

#ifdef KLEE_VERIFICATION
#  define CHUNK_LAYOUT_IMPL(pkt, len, fields, n_fields, nests, n_nests, tag) \
  packet_set_next_chunk_layout(pkt, len, fields, n_fields, nests, n_nests, tag)
#else//KLEE_VERIFICATION
#  define CHUNK_LAYOUT_IMPL(pkt, len, fields, n_fields, nests, n_nests, tag) \
  /*nothing*/
#endif//KLEE_VERIFICATION

#define CHUNK_LAYOUT_N(pkt, str_name, fields, nests)              \
  CHUNK_LAYOUT_IMPL(pkt, sizeof(struct str_name),                  \
                    fields,                                        \
                    sizeof(fields)/sizeof(fields[0]),              \
                    nests,                                         \
                    sizeof(nests)/sizeof(nests[0]),                \
                    #str_name);

#define CHUNK_LAYOUT(pkt, str_name, fields)             \
  CHUNK_LAYOUT_IMPL(pkt, sizeof(struct str_name),        \
                    fields,                              \
                    sizeof(fields)/sizeof(fields[0]),    \
                    NULL,                                \
                    0,                                   \
                    #str_name);

static inline
void nf_return_all_chunks(struct Packet* p) {
  do {
    chunks_borrowed_num--;
    packet_return_chunk(p, chunks_borrowed[chunks_borrowed_num]);
  } while(chunks_borrowed_num != 0);
}

static inline
struct ether_hdr* nf_then_get_ether_header(struct Packet* p) {
  CHUNK_LAYOUT_N(p, ether_hdr, ether_fields, ether_nested_fields);
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
  CHUNK_LAYOUT(p, ipv4_hdr, ipv4_fields);
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
      // Do not really trace the ip options chunk, as it's length
      // is unknown statically
      CHUNK_LAYOUT_IMPL(p, 1, NULL, 0, NULL, 0, "ipv4_options");
      *ip_options = (uint8_t*)nf_borrow_next_chunk(p, ip_options_length);
    }
  }
  return hdr;
}

static inline
struct tcpudp_hdr* nf_then_get_tcpudp_header(struct Packet* p) {
  CHUNK_LAYOUT(p, tcpudp_hdr, tcpudp_fields);
  return (struct tcpudp_hdr*)nf_borrow_next_chunk(p, sizeof(struct tcpudp_hdr));
}


