#include <stdbool.h>
#include <rte_ethdev.h>

bool devices_configured[STUB_DEVICES_COUNT];
bool devices_tx_setup[STUB_DEVICES_COUNT];
bool devices_rx_setup[STUB_DEVICES_COUNT];
bool devices_started[STUB_DEVICES_COUNT];
bool devices_promiscuous[STUB_DEVICES_COUNT];
struct rte_mempool* devices_rx_mempool[STUB_DEVICES_COUNT];
