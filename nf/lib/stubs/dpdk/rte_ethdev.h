#pragma once

#include <inttypes.h>
#include <stdbool.h>

#include "lib/stubs/core_stub.h"
#include "lib/packet-io.h"
#include "lib/stubs/packet-io-stub-control.h"

#include <klee/klee.h>

struct rte_eth_link {
	uint32_t link_speed;
	uint16_t link_duplex  : 1;
	uint16_t link_autoneg : 1;
	uint16_t link_status  : 1;
};

/**
 * A structure used to configure the TX features of an Ethernet port.
 */
struct rte_eth_txmode {
    // we don't care about other members
};

struct rte_eth_conf {
	struct { uint8_t hw_strip_crc; } rxmode; 
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
extern bool devices_configured[STUB_DEVICES_COUNT];
extern bool devices_tx_setup[STUB_DEVICES_COUNT];
extern bool devices_rx_setup[STUB_DEVICES_COUNT];
extern bool devices_started[STUB_DEVICES_COUNT];
extern bool devices_promiscuous[STUB_DEVICES_COUNT];

// To allocate mbufs
extern struct rte_mempool* devices_rx_mempool[STUB_DEVICES_COUNT];


static inline uint16_t
rte_eth_dev_count(void)
{
	return STUB_DEVICES_COUNT;
}

static inline int
rte_eth_dev_configure(uint16_t port_id, uint16_t nb_rx_queue, uint16_t nb_tx_queue,
			const struct rte_eth_conf* eth_conf)
{
	klee_assert(!devices_configured[port_id]);
	klee_assert(nb_rx_queue == 1); // we only support that
	klee_assert(nb_tx_queue == 1); // same
	// TODO somehow semantically check eth_conf?

	devices_configured[port_id] = true;
	return 0;
}

static inline int
rte_eth_tx_queue_setup(uint16_t port_id, uint16_t tx_queue_id,
			uint16_t nb_tx_desc, unsigned int socket_id,
			const struct rte_eth_txconf* tx_conf)
{
	klee_assert(devices_configured[port_id]);
	klee_assert(!devices_tx_setup[port_id]);
	klee_assert(tx_queue_id == 0); // we only support that
	klee_assert(socket_id == 0); // same
        klee_assert(tx_conf == NULL); // same

	devices_tx_setup[port_id] = true;
	return 0;
}

static inline int
rte_eth_rx_queue_setup(uint16_t port_id, uint16_t rx_queue_id, uint16_t nb_rx_desc,
			unsigned int socket_id, const struct rte_eth_rxconf *rx_conf,
			struct rte_mempool *mb_pool)
{
	klee_assert(devices_tx_setup[port_id]);
	klee_assert(!devices_rx_setup[port_id]);
	klee_assert(rx_queue_id == 0); // we only support that
	klee_assert(socket_id == 0); // same
	klee_assert(mb_pool != NULL);
	// TODO semantic checks for rx_conf? since we need it for the hardware verif

	devices_rx_setup[port_id] = true;
	devices_rx_mempool[port_id] = mb_pool;
	return 0;
}

static inline int
rte_eth_dev_start(uint16_t port_id)
{
	klee_assert(devices_rx_setup[port_id]);
	klee_assert(!devices_started[port_id]);

	devices_started[port_id] = true;
	return 0;
}

static inline void
rte_eth_promiscuous_enable(uint16_t port_id)
{
	klee_assert(!devices_promiscuous[port_id]);
	devices_promiscuous[port_id] = true;
}

static inline int
rte_eth_promiscuous_get(uint16_t port_id)
{
	return devices_promiscuous[port_id] ? 1 : 0;
}

static inline int
rte_eth_dev_socket_id(uint16_t port_id)
{
	klee_assert(port_id < rte_eth_dev_count());

	return 0;
}

static inline void
rte_eth_macaddr_get(uint16_t port_id, struct ether_addr *mac_addr)
{
	// TODO?
}

static inline
uint16_t
rte_eth_rx_burst(uint16_t port_id, uint16_t queue_id,
                 struct rte_mbuf **rx_pkts, uint16_t nb_pkts)
{
	klee_assert(devices_started[port_id]);
	klee_assert(queue_id == 0); // we only support that
	klee_assert(nb_pkts == 1); // same

	struct rte_mempool* pool = devices_rx_mempool[port_id];
	stub_core_mbuf_create(port_id, pool, rx_pkts);

	set_packet_receive_success(klee_int("received_a_packet"));

  bool received = packet_receive(port_id, &(**rx_pkts).buf_addr, &(**rx_pkts).pkt_len);
  return received;
}

static inline
uint16_t
rte_eth_tx_burst(uint16_t port_id, uint16_t queue_id,
                 struct rte_mbuf **tx_pkts, uint16_t nb_pkts)
{
	klee_assert(devices_started[port_id]);
	klee_assert(queue_id == 0); // we only support that
	klee_assert(nb_pkts == 1); // same

  packet_send((**tx_pkts).buf_addr, port_id);

	stub_core_mbuf_free(*tx_pkts);
	return 1;
}

//TODO: this belongs to rte_mbuf.h
// but is here to present a single dpdk-stub API.
static inline
struct rte_mbuf*
rte_pktmbuf_clone(struct rte_mbuf* frame, struct rte_mempool* clone_pool) {
  struct rte_mbuf* copy;
  bool success = stub_core_mbuf_create(frame->port, clone_pool, &copy);
  if (!success) return NULL;
  //struct rte_mbuf* copy =malloc(clone_pool->elt_size);// rte_mbuf_raw_alloc(clone_pool);

  /* memcpy(copy, frame, sizeof(struct rte_mbuf)); */
	/* struct rte_mbuf* buf_next = (struct rte_mbuf*) malloc(clone_pool->elt_size); */
	/* if (buf_next == NULL) { */
	/* 	rte_pktmbuf_free(copy); */
	/* 	return false; */
	/* } */
  /* copy->next = buf_next; */
	/* klee_forbid_access(copy->next, clone_pool->elt_size, "clone_buf_next"); */

  packet_clone(frame->buf_addr, &copy->buf_addr);
  return copy;
}
/**
 * Retrieve the contextual information of an Ethernet device.
 *
 * @param port_id
 *   The port identifier of the Ethernet device.
 * @param dev_info
 *   A pointer to a structure of type *rte_eth_dev_info* to be filled with
 *   the contextual information of the Ethernet device.
 */
void rte_eth_dev_info_get(uint16_t port_id, struct rte_eth_dev_info *dev_info);
