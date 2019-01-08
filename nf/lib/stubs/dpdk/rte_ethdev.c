#include <rte_ethdev.h>

bool devices_configured[STUB_DEVICES_COUNT];
bool devices_tx_setup[STUB_DEVICES_COUNT];
bool devices_rx_setup[STUB_DEVICES_COUNT];
bool devices_started[STUB_DEVICES_COUNT];
bool devices_promiscuous[STUB_DEVICES_COUNT];
struct rte_mempool* devices_rx_mempool[STUB_DEVICES_COUNT];


uint16_t
rte_eth_rx_burst(uint16_t port_id, uint16_t queue_id,
                 struct rte_mbuf **rx_pkts, uint16_t nb_pkts)
{
	klee_assert(devices_started[port_id]);
	klee_assert(queue_id == 0); // we only support that
	klee_assert(nb_pkts == 1); // same

	if (klee_int("received") == 0) {
		return 0;
	}

	struct rte_mempool* pool = devices_rx_mempool[port_id];
	stub_core_mbuf_create(port_id, pool, rx_pkts);
	stub_core_trace_rx(rx_pkts);

	return 1;
}

uint16_t
rte_eth_tx_burst(uint16_t port_id, uint16_t queue_id,
                 struct rte_mbuf **tx_pkts, uint16_t nb_pkts)
{
	klee_assert(devices_started[port_id]);
	klee_assert(queue_id == 0); // we only support that
	klee_assert(nb_pkts == 1); // same

	uint8_t ret = stub_core_trace_tx(*tx_pkts, port_id);
	if (ret == 0) {
		return 0;
	}

	stub_core_mbuf_free(*tx_pkts);
	return 1;
}
