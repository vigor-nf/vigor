// DPDK uses these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>

#include <rte_common.h>
#include <rte_eal.h>
#include <rte_errno.h>
#include <rte_ethdev.h>
#include <rte_lcore.h>
#include <rte_mbuf.h>

#include "libvig/nf_forward.h"
#include "libvig/nf_log.h"
#include "libvig/nf_time.h"
#include "libvig/nf_util.h"
#include "libvig/packet-io.h"
#include "router.h"

#include <inttypes.h>

// Number of RX/TX queues
static const uint16_t RX_QUEUES_COUNT = 1;
static const uint16_t TX_QUEUES_COUNT = 1;

// Queue sizes for receiving/transmitting packets
// NOT powers of 2 so that ixgbe doesn't use vector stuff
// but they have to be multiples of 8, and at least 32, otherwise the driver
// refuses
static const uint16_t RX_QUEUE_SIZE = 96;
static const uint16_t TX_QUEUE_SIZE = 96;

// Clone pool for flood()
static struct rte_mempool *clone_pool;

void flood(struct rte_mbuf *frame, uint16_t skip_device, uint16_t nb_devices,
           struct rte_mempool *clone_pool) {
  for (uint16_t device = 0; device < nb_devices; device++) {
    if (device == skip_device)
      continue;
    struct rte_mbuf *copy = rte_pktmbuf_clone(frame, clone_pool);
    if (copy == NULL) {
      rte_exit(EXIT_FAILURE, "Cannot clone a frame for flooding");
    }
    nf_send_packet(copy, device);
  }
  rte_pktmbuf_free(frame);
}

// Buffer count for mempools
static const unsigned MEMPOOL_BUFFER_COUNT = 256;

// --- Initialization ---
static int nf_init_device(uint16_t device, struct rte_mempool *mbuf_pool) {
  int retval;

  // device_conf passed to rte_eth_dev_configure cannot be NULL
  struct rte_eth_conf device_conf;
  memset(&device_conf, 0, sizeof(struct rte_eth_conf));

  // Configure the device
  retval = rte_eth_dev_configure(device, RX_QUEUES_COUNT, TX_QUEUES_COUNT,
                                 &device_conf);
  if (retval != 0) {
    return retval;
  }

  // Allocate and set up TX queues
  for (int txq = 0; txq < TX_QUEUES_COUNT; txq++) {
    retval = rte_eth_tx_queue_setup(device, txq, TX_QUEUE_SIZE,
                                    rte_eth_dev_socket_id(device),
                                    NULL // config (NULL = default)
    );
    if (retval != 0) {
      return retval;
    }
  }

  // Allocate and set up RX queues
  // with rx_free_thresh = 1 so that internal descriptors are replenished
  // always, i.e. 1 mbuf is taken (for RX) from the pool and 1 is put back (when
  // freeing),
  //      at each iteration, which avoids havocing problems
  struct rte_eth_rxconf rx_conf = { 0 };
  rx_conf.rx_free_thresh = 1;
  for (int rxq = 0; rxq < RX_QUEUES_COUNT; rxq++) {
    retval = rte_eth_rx_queue_setup(device, rxq, RX_QUEUE_SIZE,
                                    rte_eth_dev_socket_id(device), &rx_conf,
                                    mbuf_pool);
    if (retval != 0) {
      return retval;
    }
  }

  // Start the device
  retval = rte_eth_dev_start(device);
  if (retval != 0) {
    return retval;
  }

  // Enable RX in promiscuous mode, just in case
  rte_eth_promiscuous_enable(device);
  if (rte_eth_promiscuous_get(device) != 1) {
    return retval;
  }

  return 0;
}

// --- Per-core work ---

static void lcore_main(void) {

  // TODO is this check useful?
  for (uint16_t device = 0; device < rte_eth_dev_count(); device++) {
    if (rte_eth_dev_socket_id(device) > 0 &&
        rte_eth_dev_socket_id(device) != (int)rte_socket_id()) {
      NF_INFO("Device %" PRIu8 " is on remote NUMA node to polling thread.",
              device);
    }
  }

  nf_core_init();

  NF_INFO("Core %u forwarding packets.", rte_lcore_id());

  while (likely(1)) {

    unsigned VIGOR_DEVICES_COUNT = rte_eth_dev_count();

    for (uint16_t VIGOR_DEVICE = 0; VIGOR_DEVICE < VIGOR_DEVICES_COUNT;
         VIGOR_DEVICE++) {

      struct rte_mbuf *mbuf;
      if (likely(nf_receive_packet(VIGOR_DEVICE, &mbuf))) {

        uint16_t dst_device =
            nf_core_process(mbuf, 0); // don't need the time for the router
        nf_return_all_chunks(mbuf_pkt(mbuf));

        if (unlikely(dst_device == FLOOD_FRAME)) {

          flood(mbuf, VIGOR_DEVICE, VIGOR_DEVICES_COUNT, clone_pool);
        } else {

          uint16_t actual_tx_len = rte_eth_tx_burst(dst_device, 0, &mbuf, 1);

          if (unlikely(actual_tx_len == 0)) {

            rte_pktmbuf_free(mbuf);
          }
        }
      }
    }
  }
}

// --- Main ---

int main(int argc, char *argv[]) {
  // Initialize the Environment Abstraction Layer (EAL)
  int ret = rte_eal_init(argc, argv);
  if (ret < 0) {
    rte_exit(EXIT_FAILURE, "Error with EAL initialization, ret=%d\n", ret);
  }
  argc -= ret;
  argv += ret;

#ifdef KLEE_VERIFICATION
  // Attach stub driver (note that hardware stub is autodetected, no need to
  // attach)
  stub_driver_attach();
#endif

  // NF-specific config
  nf_config_init(argc, argv);
  nf_print_config();

  // Create a memory pool
  unsigned nb_devices = rte_eth_dev_count();
  struct rte_mempool *mbuf_pool = rte_pktmbuf_pool_create(
      "MEMPOOL",                         // name
      MEMPOOL_BUFFER_COUNT * nb_devices, // #elements
      0, // cache size (per-lcore, not useful in a single-threaded app)
      0, // application private area size
      RTE_MBUF_DEFAULT_BUF_SIZE, // data buffer size
      rte_socket_id()            // socket ID
  );
  if (mbuf_pool == NULL) {
    rte_exit(EXIT_FAILURE, "Cannot create mbuf pool: %s\n",
             rte_strerror(rte_errno));
  }

  // Create another pool for the flood() cloning
  clone_pool =
      rte_pktmbuf_pool_create("clone_pool",         // name
                              MEMPOOL_BUFFER_COUNT, // #elements
                              0, // cache size (same remark as above)
                              0, // application private data size
                              RTE_MBUF_DEFAULT_BUF_SIZE, // data buffer size
                              rte_socket_id()            // socket ID
      );
  if (clone_pool == NULL) {
    rte_exit(EXIT_FAILURE, "Cannot create mbuf clone pool: %s\n",
             rte_strerror(rte_errno));
  }

  // Initialize all devices
  for (uint16_t device = 0; device < nb_devices; device++) {
    ret = nf_init_device(device, mbuf_pool);
    if (ret == 0) {
      NF_INFO("Initialized device %" PRIu8 ".", device);
    } else {
      rte_exit(EXIT_FAILURE, "Cannot init device %" PRIu8 ", ret=%d", device,
               ret);
    }
  }

  // Run!
  // ...in single-threaded mode, that is.
  lcore_main();

  return 0;
}
