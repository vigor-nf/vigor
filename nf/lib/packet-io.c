#include "packet-io.h"

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

void packet_return_all_chunks(struct Packet* p) {
  //Do nothing. needed only for verification
}

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

void packet_send(struct Packet* p, uint16_t dst_device) {
  uint16_t actual_tx_len = rte_eth_tx_burst(dst_device, 0, &p->mbuf, 1);
  if (actual_tx_len == 0) {
    rte_pktmbuf_free(p->mbuf);
  }
}

// Flood method for the bridge
#ifndef KLEE_VERIFICATION
extern struct rte_mempool* clone_pool;
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

void packet_free(struct Packet* p) {
  rte_pktmbuf_free(p->mbuf);
}
