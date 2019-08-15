// DPDK uses these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>

#include <rte_common.h>
#include <rte_eal.h>
#include <rte_errno.h>
#include <rte_ethdev.h>
#include <rte_lcore.h>
#include <rte_mbuf.h>

#include "libvig/boilerplate_util.h"
#include "nf.h"
#include "libvig/nf_log.h"
#include "libvig/nf_time.h"
#include "libvig/nf_util.h"
#include "libvig/packet-io.h"

#ifdef KLEE_VERIFICATION
#  include "libvig/stubs/time_stub_control.h"
#  include "libvig/stubs/hardware_stub.h"
#  include <klee/klee.h>
#endif//KLEE_VERIFICATION

#ifdef DSOS
#  define MAIN nf_main
#else//DSOS
#  define MAIN main
#endif//DSOS

#include <inttypes.h>

#ifdef KLEE_VERIFICATION
#  define VIGOR_LOOP_BEGIN \
    unsigned _vigor_lcore_id = rte_lcore_id(); \
    vigor_time_t _vigor_start_time = start_time(); \
    int _vigor_loop_termination = klee_int("loop_termination"); \
    unsigned VIGOR_DEVICES_COUNT;                                       \
    klee_possibly_havoc(&VIGOR_DEVICES_COUNT, sizeof(VIGOR_DEVICES_COUNT), "VIGOR_DEVICES_COUNT"); \
    vigor_time_t VIGOR_NOW;                                                   \
    klee_possibly_havoc(&VIGOR_NOW, sizeof(VIGOR_NOW), "VIGOR_NOW");    \
    unsigned VIGOR_DEVICE;                                              \
    klee_possibly_havoc(&VIGOR_DEVICE, sizeof(VIGOR_DEVICE), "VIGOR_DEVICE"); \
    unsigned _d;                                                        \
    klee_possibly_havoc(&_d, sizeof(_d), "_d");                         \
    while(klee_induce_invariants() & _vigor_loop_termination) { \
      nf_loop_iteration_border(_vigor_lcore_id, _vigor_start_time);      \
      VIGOR_NOW = current_time(); \
      /* concretize the device to avoid leaking symbols into DPDK */ \
      VIGOR_DEVICES_COUNT = rte_eth_dev_count(); \
      VIGOR_DEVICE = klee_range(0, VIGOR_DEVICES_COUNT, "VIGOR_DEVICE"); \
      for(_d = 0; _d < VIGOR_DEVICES_COUNT; _d++) if (VIGOR_DEVICE == _d) { VIGOR_DEVICE = _d; break; } \
      stub_hardware_receive_packet(VIGOR_DEVICE);
#define VIGOR_LOOP_END                                \
      stub_hardware_reset_receive(VIGOR_DEVICE);          \
      nf_loop_iteration_border(_vigor_lcore_id, VIGOR_NOW);  \
      }
#else//KLEE_VERIFICATION
#  define VIGOR_LOOP_BEGIN \
    while (1) { \
      vigor_time_t VIGOR_NOW = current_time(); \
      unsigned VIGOR_DEVICES_COUNT = rte_eth_dev_count(); \
      for (uint16_t VIGOR_DEVICE = 0; VIGOR_DEVICE < VIGOR_DEVICES_COUNT; VIGOR_DEVICE++) {
#  define VIGOR_LOOP_END } }
#endif//KLEE_VERIFICATION


// Number of RX/TX queues
static const uint16_t RX_QUEUES_COUNT = 1;
static const uint16_t TX_QUEUES_COUNT = 1;

// Queue sizes for receiving/transmitting packets
// NOT powers of 2 so that ixgbe doesn't use vector stuff
// but they have to be multiples of 8, and at least 32, otherwise the driver refuses
static const uint16_t RX_QUEUE_SIZE = 96;
static const uint16_t TX_QUEUE_SIZE = 96;

void
flood(struct rte_mbuf* frame, uint16_t skip_device, uint16_t nb_devices) {
  rte_mbuf_refcnt_set(frame, nb_devices - 1);
  int total_sent = 0;
  for (uint16_t device = 0; device < nb_devices; device++) {
    if (device == skip_device) continue;
    total_sent += rte_eth_tx_burst(device, 0, &frame, 1);
  }
  if (total_sent != nb_devices - 1) {
    rte_pktmbuf_free(frame);
  }
}

// Buffer count for mempools
static const unsigned MEMPOOL_BUFFER_COUNT = 256;

// --- Initialization ---
static int
nf_init_device(uint16_t device, struct rte_mempool *mbuf_pool)
{
  int retval;

  // device_conf passed to rte_eth_dev_configure cannot be NULL
  struct rte_eth_conf device_conf;
  memset(&device_conf, 0, sizeof(struct rte_eth_conf));
  device_conf.rxmode.hw_strip_crc = 1;

  // Configure the device
  retval = rte_eth_dev_configure(
    device,
    RX_QUEUES_COUNT,
    TX_QUEUES_COUNT,
    &device_conf
  );
  if (retval != 0) {
    return retval;
  }

  // Allocate and set up TX queues
  for (int txq = 0; txq < TX_QUEUES_COUNT; txq++) {
    retval = rte_eth_tx_queue_setup(
      device,
      txq,
      TX_QUEUE_SIZE,
      rte_eth_dev_socket_id(device),
      NULL
    );
    if (retval != 0) {
      return retval;
    }
  }

  // Allocate and set up RX queues
  for (int rxq = 0; rxq < RX_QUEUES_COUNT; rxq++) {
    retval = rte_eth_rx_queue_setup(
      device,
      rxq,
      RX_QUEUE_SIZE,
      rte_eth_dev_socket_id(device),
      NULL, // default config
      mbuf_pool
    );
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

static void
lcore_main(void)
{
  for (uint16_t device = 0; device < rte_eth_dev_count(); device++) {
    if (rte_eth_dev_socket_id(device) > 0 && rte_eth_dev_socket_id(device) != (int) rte_socket_id()) {
      NF_INFO("Device %" PRIu8 " is on remote NUMA node to polling thread.", device);
    }
  }

  nf_init();

  NF_INFO("Core %u forwarding packets.", rte_lcore_id());

  VIGOR_LOOP_BEGIN
    struct rte_mbuf* mbuf;
    if (nf_receive_packet(VIGOR_DEVICE, &mbuf)) {
      uint16_t dst_device = nf_process(mbuf, VIGOR_NOW);
      nf_return_all_chunks(mbuf_pkt(mbuf));

      if (dst_device == VIGOR_DEVICE) {
        nf_free_packet(mbuf);
      } else if (dst_device == FLOOD_FRAME) {
        flood(mbuf, VIGOR_DEVICE, VIGOR_DEVICES_COUNT);
      } else {
        concretize_devices(&dst_device, rte_eth_dev_count());
        nf_send_packet(mbuf, dst_device);
      }
    }
  VIGOR_LOOP_END
}


// --- Main ---

int
MAIN(int argc, char* argv[])
{
  // Initialize the Environment Abstraction Layer (EAL)
  int ret = rte_eal_init(argc, argv);
  if (ret < 0) {
    rte_exit(EXIT_FAILURE, "Error with EAL initialization, ret=%d\n", ret);
  }
  argc -= ret;
  argv += ret;

  // NF-specific config
  nf_config_init(argc, argv);
  nf_config_print();

  // Create a memory pool
  unsigned nb_devices = rte_eth_dev_count();
  struct rte_mempool* mbuf_pool = rte_pktmbuf_pool_create(
    "MEMPOOL", // name
    MEMPOOL_BUFFER_COUNT * nb_devices, // #elements
    0, // cache size (per-lcore, not useful in a single-threaded app)
    0, // application private area size
    RTE_MBUF_DEFAULT_BUF_SIZE, // data buffer size
    rte_socket_id() // socket ID
  );
  if (mbuf_pool == NULL) {
    rte_exit(EXIT_FAILURE, "Cannot create mbuf pool: %s\n", rte_strerror(rte_errno));
  }

  // Initialize all devices
  for (uint16_t device = 0; device < nb_devices; device++) {
    ret = nf_init_device(device, mbuf_pool);
    if (ret == 0) {
      NF_INFO("Initialized device %" PRIu16 ".", device);
    } else {
      rte_exit(EXIT_FAILURE, "Cannot init device %" PRIu16 ", ret=%d", device, ret);
    }
  }

  // Run!
  // ...in single-threaded mode, that is.
  lcore_main();

  return 0;
}
