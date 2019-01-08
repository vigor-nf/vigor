#include <klee/klee.h>
#include "lib/stubs/containers/str-descr.h"
#include "lib/packet-io.h"

struct Packet {
  struct rte_mbuf* mbuf;
  char* unread_buf;
};

static struct Packet global_current_packet;

void packet_init(struct Packet* p) {
  assert(p->mbuf != NULL);
  p->unread_buf = (char*)p->mbuf->buf_addr + p->mbuf->data_off;
}

// The main IO primitive.
char* packet_borrow_next_chunk(struct Packet* p, size_t length) {
  //TODO: check for overflowing the current mbuf.
  char* ret = p->unread_buf;
  p->unread_buf += length;
  return ret;
}

void packet_return_chunk(struct Packet* p, char* chunk) {
  p->unread_buf = chunk;
}

bool packet_receive(uint16_t src_device, struct Packet** p) {
  struct rte_mbuf* buf = NULL;
  uint16_t actual_rx_len = rte_eth_rx_burst(src_device, 0, &buf, 1);

  if (actual_rx_len != 0) {
    *p = &global_current_packet;
    (*p)->mbuf = buf;
    packet_init(*p);
    return true;
  } else {
    return false;
  }
}

void packet_send(struct Packet* p, uint16_t dst_device) {
  uint16_t actual_tx_len = rte_eth_tx_burst(dst_device, 0, &p->mbuf, 1);
  if (actual_tx_len == 0) {
    rte_pktmbuf_free(p->mbuf);
  }
}

void packet_free(struct Packet* p) {
  rte_pktmbuf_free(p->mbuf);
}

bool packet_is_ipv4(struct Packet* p) {
  return RTE_ETH_IS_IPV4_HDR(p->mbuf->packet_type);
}

uint16_t packet_get_port(struct Packet* p) {
  return p->mbuf->port;
}

//VVV necessary just for tracing the flood function. to be removed

// TODO DEDUPLICATE THIS
static struct str_field_descr mbuf_descrs[] = {
  //Do not forget about "buf_addr" -- it is a pointer that is why it is not listed here.
  {offsetof(struct rte_mbuf, buf_iova), sizeof(rte_iova_t), "buf_iova"},
  {offsetof(struct rte_mbuf, data_off), sizeof(uint16_t), "data_off"},
  {offsetof(struct rte_mbuf, refcnt), sizeof(uint16_t), "refcnt"},
  {offsetof(struct rte_mbuf, nb_segs), sizeof(uint16_t), "nb_segs"},
  {offsetof(struct rte_mbuf, port), sizeof(uint16_t), "port"},
  {offsetof(struct rte_mbuf, ol_flags), sizeof(uint64_t), "ol_flags"},
  {offsetof(struct rte_mbuf, packet_type), sizeof(uint32_t), "packet_type"},
  {offsetof(struct rte_mbuf, pkt_len), sizeof(uint32_t), "pkt_len"},
  {offsetof(struct rte_mbuf, data_len), sizeof(uint16_t), "data_len"},
  {offsetof(struct rte_mbuf, vlan_tci), sizeof(uint16_t), "vlan_tci"},
  {offsetof(struct rte_mbuf, hash), sizeof(uint32_t), "hash"},
  {offsetof(struct rte_mbuf, vlan_tci_outer), sizeof(uint16_t), "vlan_tci_outer"},
  {offsetof(struct rte_mbuf, buf_len), sizeof(uint16_t), "buf_len"},
  {offsetof(struct rte_mbuf, timestamp), sizeof(uint64_t), "timestamp"},
  {offsetof(struct rte_mbuf, udata64), sizeof(uint64_t), "udata64"},
  {offsetof(struct rte_mbuf, pool), sizeof(struct rte_mempool*), "pool"},
  {offsetof(struct rte_mbuf, next), sizeof(struct rte_mbuf*), "next"},
  {offsetof(struct rte_mbuf, tx_offload), sizeof(uint64_t), "tx_offload"},
  {offsetof(struct rte_mbuf, priv_size), sizeof(uint16_t), "priv_size"},
  {offsetof(struct rte_mbuf, timesync), sizeof(uint16_t), "timesync"},
  {offsetof(struct rte_mbuf, seqn), sizeof(uint32_t), "seqn"},
};
static struct nested_field_descr stub_mbuf_content_nested[] = {
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, ether_type), sizeof(uint16_t), "ether_type"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), sizeof(struct ether_addr), "d_addr"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), sizeof(struct ether_addr), "s_addr"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, version_ihl), sizeof(uint8_t), "version_ihl"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, type_of_service), sizeof(uint8_t), "type_of_service"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, total_length), sizeof(uint16_t), "total_length"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, packet_id), sizeof(uint16_t), "packet_id"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, fragment_offset), sizeof(uint16_t), "fragment_offset"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, time_to_live), sizeof(uint8_t), "time_to_live"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, next_proto_id), sizeof(uint8_t), "next_proto_id"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, hdr_checksum), sizeof(uint16_t), "hdr_checksum"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, src_addr), sizeof(uint32_t), "src_addr"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, dst_addr), sizeof(uint32_t), "dst_addr"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, src_port), sizeof(uint16_t), "src_port"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, sent_seq), sizeof(uint32_t), "sent_seq"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, recv_ack), sizeof(uint32_t), "recv_ack"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, data_off), sizeof(uint8_t), "data_off"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, tcp_flags), sizeof(uint8_t), "tcp_flags"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, rx_win), sizeof(uint16_t), "rx_win"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, cksum), sizeof(uint16_t), "cksum"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, tcp_urp), sizeof(uint16_t), "tcp_urp"},
};
static struct nested_nested_field_descr stub_mbuf_content_n2[] = {
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), 0, sizeof(uint8_t) * 6, "addr_bytes"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), 0, sizeof(uint8_t) * 6, "addr_bytes"},
};
#define KLEE_TRACE_MBUF(m_ptr, mname, dir)                                                                                             \
  klee_trace_param_ptr_directed(m_ptr, sizeof(*m_ptr), mname, dir);                                                                    \
  klee_trace_param_ptr_field_directed(m_ptr, offsetof(struct rte_mbuf, buf_addr), sizeof(struct stub_mbuf_content*), "buf_addr", dir); \
  for (int i = 0; i < sizeof(mbuf_descrs)/sizeof(mbuf_descrs[0]); ++i) {                                                               \
    klee_trace_param_ptr_field_directed(m_ptr,                                                                                         \
                                        mbuf_descrs[i].offset,                                                                         \
                                        mbuf_descrs[i].width,                                                                          \
                                        mbuf_descrs[i].name,                                                                           \
                                        dir);                                                                                          \
  }
#define KLEE_TRACE_MBUF_CONTENT(u_ptr, dir)                                                                             \
  klee_trace_extra_ptr(u_ptr, sizeof(struct stub_mbuf_content), "user_buf_addr", "", dir);                              \
  klee_trace_extra_ptr_field(u_ptr, offsetof(struct stub_mbuf_content, ether), sizeof(struct ether_hdr), "ether", dir); \
  klee_trace_extra_ptr_field(u_ptr, offsetof(struct stub_mbuf_content, ipv4), sizeof(struct ipv4_hdr), "ipv4", dir);    \
  klee_trace_extra_ptr_field(u_ptr, offsetof(struct stub_mbuf_content, tcp), sizeof(struct tcp_hdr), "tcp", dir);       \
  for (int i = 0; i < sizeof(stub_mbuf_content_nested)/sizeof(stub_mbuf_content_nested[0]); ++i) {                      \
    klee_trace_extra_ptr_nested_field(u_ptr,                                                                            \
                                      stub_mbuf_content_nested[i].base_offset,                                          \
                                      stub_mbuf_content_nested[i].offset,                                               \
                                      stub_mbuf_content_nested[i].width,                                                \
                                      stub_mbuf_content_nested[i].name,                                                 \
                                      dir);                                                                             \
  }                                                                                                                     \
  for (int i = 0; i < sizeof(stub_mbuf_content_n2)/sizeof(stub_mbuf_content_n2[0]); ++i) {                              \
    klee_trace_extra_ptr_nested_nested_field                                                                            \
      (u_ptr,                                                                                                           \
       stub_mbuf_content_n2[i].base_base_offset,                                                                        \
       stub_mbuf_content_n2[i].base_offset,                                                                             \
       stub_mbuf_content_n2[i].offset,                                                                                  \
       stub_mbuf_content_n2[i].width,                                                                                   \
       stub_mbuf_content_n2[i].name,                                                                                    \
       dir);                                                                                                            \
  }
// flooding is necessary for the bridge to function
// TODO why does this even exist?
void packet_flood(struct Packet* p,
                  uint16_t skip_device,
                  uint16_t nb_devices,
                  struct rte_mempool* clone_pool) {
  klee_trace_ret();
  struct rte_mbuf* frame = p->mbuf;
  KLEE_TRACE_MBUF(frame, "frame", TD_IN);
  KLEE_TRACE_MBUF_CONTENT(frame->buf_addr, TD_IN);
  klee_trace_param_i32(skip_device, "skip_device");
  klee_trace_param_i32(nb_devices, "nb_devices");
  klee_trace_param_ptr_just_ptr(clone_pool, sizeof(struct rte_mempool*), "clone_pool");
  //  klee_forbid_access(frame->buf_addr, sizeof(struct stub_mbuf_content),
  //                     "pkt flooded");
  //  klee_forbid_access(frame,
  //                     sizeof(struct rte_mbuf),
  //                     "pkt flooded");
}
