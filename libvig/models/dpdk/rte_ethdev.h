#pragma once

#include <inttypes.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include <rte_byteorder.h>
#include <rte_mbuf.h>
#include <rte_mbuf_ptype.h>
#include <rte_memory.h>
#include <rte_ethdev.h>

#include "libvig/verified/packet-io.h"
#include "libvig/models/str-descr.h"
#include "libvig/models/verified/packet-io-control.h"

#include <klee/klee.h>


struct rte_eth_link {
  uint32_t link_speed;
  uint16_t link_duplex : 1;
  uint16_t link_autoneg : 1;
  uint16_t link_status : 1;
};

const static uint32_t max_send_failures = 2;

/**
 * A structure used to configure the TX features of an Ethernet port.
 */
struct rte_eth_txmode {
  // we don't care about other members
};

struct rte_eth_conf {
  struct {
    uint8_t hw_strip_crc;
  } rxmode;
  struct rte_eth_txmode txmode;

  /* Don't care about other members */
};
struct rte_eth_rxconf {
  uint16_t rx_free_thresh;
  // we don't care about other members
};

struct rte_eth_txconf {
  // we don't care about other members
};

/**
 * Ethernet device information
 */
struct rte_eth_dev_info {
  /* Device per port TX offload capabilities. */
  uint64_t tx_offload_capa;
  // We don't care about other members
};

// Sanity checks
// Documentation of rte_ethdev indicates the configure/tx/rx/started order
bool devices_configured[STUB_DEVICES_COUNT];
bool devices_tx_setup[STUB_DEVICES_COUNT];
bool devices_rx_setup[STUB_DEVICES_COUNT];
bool devices_started[STUB_DEVICES_COUNT];
int devices_promiscuous[STUB_DEVICES_COUNT];

// To allocate mbufs
struct rte_mempool *devices_rx_mempool[STUB_DEVICES_COUNT];

static inline uint16_t rte_eth_dev_count_avail(void) { return STUB_DEVICES_COUNT; }

static inline int rte_eth_dev_configure(uint16_t port_id, uint16_t nb_rx_queue,
                                        uint16_t nb_tx_queue,
                                        const struct rte_eth_conf *eth_conf) {
  klee_assert(!devices_configured[port_id]);
  klee_assert(nb_rx_queue == 1); // we only support that
  klee_assert(nb_tx_queue == 1); // same
  // TODO somehow semantically check eth_conf?

  devices_configured[port_id] = true;
  devices_promiscuous[port_id] = 0;
  return 0;
}

static inline int rte_eth_tx_queue_setup(uint16_t port_id, uint16_t tx_queue_id,
                                         uint16_t nb_tx_desc,
                                         unsigned int socket_id,
                                         const struct rte_eth_txconf *tx_conf) {
  klee_assert(devices_configured[port_id]);
  klee_assert(!devices_tx_setup[port_id]);
  klee_assert(tx_queue_id == 0); // we only support that
  klee_assert(socket_id == 0);   // same
  klee_assert(tx_conf == NULL);  // same

  devices_tx_setup[port_id] = true;
  return 0;
}

static inline int rte_eth_rx_queue_setup(uint16_t port_id, uint16_t rx_queue_id,
                                         uint16_t nb_rx_desc,
                                         unsigned int socket_id,
                                         const struct rte_eth_rxconf *rx_conf,
                                         struct rte_mempool *mb_pool) {
  klee_assert(devices_tx_setup[port_id]);
  klee_assert(!devices_rx_setup[port_id]);
  klee_assert(rx_queue_id == 0); // we only support that
  klee_assert(socket_id == 0);   // same
  klee_assert(mb_pool != NULL);
  // TODO semantic checks for rx_conf? since we need it for the hardware verif

  devices_rx_setup[port_id] = true;
  devices_rx_mempool[port_id] = mb_pool;
  return 0;
}

static inline int rte_eth_dev_start(uint16_t port_id) {
  klee_assert(devices_rx_setup[port_id]);
  klee_assert(!devices_started[port_id]);

  devices_started[port_id] = true;
  return 0;
}

static inline void rte_eth_promiscuous_enable(uint16_t port_id) {
  klee_assert(devices_configured[port_id]);
  klee_assert(devices_promiscuous[port_id] == 0);
  devices_promiscuous[port_id] = 1;
}

static inline int rte_eth_promiscuous_get(uint16_t port_id) {
  return devices_promiscuous[port_id];
}

static inline int rte_eth_dev_socket_id(uint16_t port_id) {
  klee_assert(port_id < rte_eth_dev_count_avail());

  return 0;
}

static inline void rte_eth_macaddr_get(uint16_t port_id,
                                       struct rte_ether_addr *mac_addr) {
  // TODO?
}

static inline uint16_t rte_eth_rx_burst(uint16_t port_id, uint16_t queue_id,
                                        struct rte_mbuf **rx_pkts,
                                        uint16_t nb_pkts) {
  klee_assert(devices_started[port_id]);
  klee_assert(queue_id == 0); // we only support that
  klee_assert(nb_pkts == 1);  // same

  struct rte_mempool *pool = devices_rx_mempool[port_id];
  uint16_t priv_size = rte_pktmbuf_priv_size(pool);
  uint16_t mbuf_size = sizeof(struct rte_mbuf) + priv_size;
  uint16_t buf_len = rte_pktmbuf_data_room_size(pool);

  *rx_pkts = rte_mbuf_raw_alloc(pool);
  if (*rx_pkts == NULL) {
    return false;
  }

  struct rte_mbuf *buf_symbol = (struct rte_mbuf *)malloc(pool->elt_size);
  if (buf_symbol == NULL) {
    rte_pktmbuf_free(*rx_pkts);
    return false;
  }

  // Make the packet symbolic
  klee_make_symbolic(buf_symbol, pool->elt_size, "buf_value");
  memcpy(*rx_pkts, buf_symbol, pool->elt_size);
  free(buf_symbol);

  // Explicitly make the content symbolic - validator depends on an user_buf
  // symbol for the proof
  klee_assert(MBUF_MIN_SIZE <= pool->elt_size);
  void *buf_content_symbol = malloc(pool->elt_size);
  if (buf_content_symbol == NULL) {
    rte_pktmbuf_free(*rx_pkts);
    return false;
  }
  klee_make_symbolic(buf_content_symbol, pool->elt_size, "user_buf");
  memcpy((char *)*rx_pkts + mbuf_size, buf_content_symbol,
         MBUF_MIN_SIZE);
  free(buf_content_symbol);

  // We do not support chained mbufs for now, make sure the NF doesn't touch
  // them
  struct rte_mbuf *buf_next = (struct rte_mbuf *)malloc(pool->elt_size);
  if (buf_next == NULL) {
    rte_pktmbuf_free(*rx_pkts);
    return false;
  }
  klee_forbid_access(buf_next, pool->elt_size, "buf_next");

  uint16_t packet_length = klee_int("pkt_len");
  uint16_t data_length = klee_int("data_len");

  klee_assume(data_length <= packet_length);
  klee_assume(sizeof(struct rte_ether_hdr) <= data_length);

  // Keep concrete values for what a driver guarantees
  // (assignments are in the same order as the rte_mbuf declaration)
  (*rx_pkts)->buf_addr = (char *)(*rx_pkts) + mbuf_size;
  (*rx_pkts)->buf_iova = (rte_iova_t)(*rx_pkts)->buf_addr; // we assume VA = PA
  // TODO: make data_off symbolic (but then we get symbolic pointer addition...)
  // Alternative: Somehow prove that the code never touches anything outside of
  // the [data_off, data_off+data_len] range...
  (*rx_pkts)->data_off = 0;
  (*rx_pkts)->refcnt = 1;
  (*rx_pkts)->nb_segs = 1;
  (*rx_pkts)->port = port_id;
  (*rx_pkts)->ol_flags = 0;
  // packet_type is symbolic, NFs should use the content of the packet as the
  // source of truth
  (*rx_pkts)->pkt_len = packet_length;
  (*rx_pkts)->data_len = data_length;
  // vlan_tci is symbolic
  // hash is symbolic
  // vlan_tci_outer is symbolic
  (*rx_pkts)->buf_len = (uint16_t)buf_len;
  // timestamp is symbolic
  (*rx_pkts)->udata64 = 0;
  (*rx_pkts)->pool = pool;
  (*rx_pkts)->next = buf_next;
  // tx_offload is symbolic
  (*rx_pkts)->priv_size = priv_size;
  // timesync is symbolic
  // seqn is symbolic

  rte_mbuf_sanity_check(*rx_pkts, 1 /* is head mbuf */);

  set_packet_receive_success(klee_int("received_a_packet"));

  bool received =
      packet_receive(port_id, &(**rx_pkts).buf_addr, &(**rx_pkts).pkt_len);
  return received;
}

static inline uint16_t rte_eth_tx_burst(uint16_t port_id, uint16_t queue_id,
                                        struct rte_mbuf **tx_pkts,
                                        uint16_t nb_pkts) {
  klee_assert(devices_started[port_id]);
  klee_assert(queue_id == 0); // we only support that
  klee_assert(nb_pkts == 1);  // same

  packet_send(tx_pkts[0]->buf_addr, port_id);

  tx_pkts[0]->refcnt--;
  if (tx_pkts[0]->refcnt == 0) {
    // Undo our pseudo-chain trickery
    klee_allow_access(tx_pkts[0]->next, tx_pkts[0]->pool->elt_size);
    free(tx_pkts[0]->next);
    tx_pkts[0]->next = NULL;
    rte_mbuf_raw_free(tx_pkts[0]);
  }
  return 1; // Assume the NIC will always accept the packet for a send.
}

