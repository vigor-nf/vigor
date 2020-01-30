#include <inttypes.h>
// DPDK uses these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>

#include <rte_common.h>
#include <rte_eal.h>
#include <rte_errno.h>
#include <rte_ethdev.h>
#include <rte_lcore.h>
#include <rte_mbuf.h>

#include "libvig/verified/boilerplate-util.h"
#include "libvig/verified/packet-io.h"
#include "nf-log.h"
#include "nf-util.h"
#include "nf.h"

#ifdef KLEE_VERIFICATION
#  include "libvig/models/hardware.h"
#  include "libvig/models/verified/vigor-time-control.h"
#  include <klee/klee.h>
#endif // KLEE_VERIFICATION

#ifdef VIGOR_DEBUG_PERF
#  include <stdio.h>
#  include "papi.h"
#  if VIGOR_BATCH_SIZE == 1
#    error Batch and perf debugging are not supported together
#  endif
#endif

#ifdef NFOS
#  define MAIN nf_main
#else // NFOS
#  define MAIN main
#endif // NFOS

#ifndef VIGOR_BATCH_SIZE
#  define VIGOR_BATCH_SIZE 1
#endif

#ifdef KLEE_VERIFICATION
#  define VIGOR_LOOP_BEGIN                                                     \
    unsigned _vigor_lcore_id = rte_lcore_id();                                 \
    vigor_time_t _vigor_start_time = start_time();                             \
    int _vigor_loop_termination = klee_int("loop_termination");                \
    unsigned VIGOR_DEVICES_COUNT;                                              \
    klee_possibly_havoc(&VIGOR_DEVICES_COUNT, sizeof(VIGOR_DEVICES_COUNT),     \
                        "VIGOR_DEVICES_COUNT");                                \
    vigor_time_t VIGOR_NOW;                                                    \
    klee_possibly_havoc(&VIGOR_NOW, sizeof(VIGOR_NOW), "VIGOR_NOW");           \
    unsigned VIGOR_DEVICE;                                                     \
    klee_possibly_havoc(&VIGOR_DEVICE, sizeof(VIGOR_DEVICE), "VIGOR_DEVICE");  \
    unsigned _d;                                                               \
    klee_possibly_havoc(&_d, sizeof(_d), "_d");                                \
    while (klee_induce_invariants() & _vigor_loop_termination) {               \
      nf_loop_iteration_border(_vigor_lcore_id, _vigor_start_time);            \
      VIGOR_NOW = current_time();                                              \
      /* concretize the device to avoid leaking symbols into DPDK */           \
      VIGOR_DEVICES_COUNT = rte_eth_dev_count();                               \
      VIGOR_DEVICE = klee_range(0, VIGOR_DEVICES_COUNT, "VIGOR_DEVICE");       \
      for (_d = 0; _d < VIGOR_DEVICES_COUNT; _d++)                             \
        if (VIGOR_DEVICE == _d) {                                              \
          VIGOR_DEVICE = _d;                                                   \
          break;                                                               \
        }                                                                      \
      stub_hardware_receive_packet(VIGOR_DEVICE);
#  define VIGOR_LOOP_END                                                       \
    stub_hardware_reset_receive(VIGOR_DEVICE);                                 \
    nf_loop_iteration_border(_vigor_lcore_id, VIGOR_NOW);                      \
    }
#else // KLEE_VERIFICATION
#  define VIGOR_LOOP_BEGIN                                                     \
    while (1) {                                                                \
      vigor_time_t VIGOR_NOW = current_time();                                 \
      unsigned VIGOR_DEVICES_COUNT = rte_eth_dev_count();                      \
      for (uint16_t VIGOR_DEVICE = 0; VIGOR_DEVICE < VIGOR_DEVICES_COUNT;      \
           VIGOR_DEVICE++) {
#  define VIGOR_LOOP_END                                                       \
    }                                                                          \
    }
#endif // KLEE_VERIFICATION

// Number of RX/TX queues
static const uint16_t RX_QUEUES_COUNT = 1;
static const uint16_t TX_QUEUES_COUNT = 1;

// Queue sizes for receiving/transmitting packets
// NOT powers of 2 so that ixgbe doesn't use vector stuff
// but they have to be multiples of 8, and at least 32, otherwise the driver
// refuses
static const uint16_t RX_QUEUE_SIZE = 96;
static const uint16_t TX_QUEUE_SIZE = 96;

void flood(struct rte_mbuf *frame, uint16_t skip_device, uint16_t nb_devices) {
  rte_mbuf_refcnt_set(frame, nb_devices - 1);
  int total_sent = 0;
  for (uint16_t device = 0; device < nb_devices; device++) {
    if (device == skip_device)
      continue;
    total_sent += rte_eth_tx_burst(device, 0, &frame, 1);
  }
  if (total_sent != nb_devices - 1) {
    rte_pktmbuf_free(frame);
  }
}

// Buffer count for mempools
static const unsigned MEMPOOL_BUFFER_COUNT = 256;

// --- Initialization ---
static int nf_init_device(uint16_t device, struct rte_mempool *mbuf_pool) {
  int retval;

  // device_conf passed to rte_eth_dev_configure cannot be NULL
  struct rte_eth_conf device_conf = {0};
  device_conf.rxmode.hw_strip_crc = 1;

  // Configure the device
  retval = rte_eth_dev_configure(device, RX_QUEUES_COUNT, TX_QUEUES_COUNT,
                                 &device_conf);
  if (retval != 0) {
    return retval;
  }

  // Allocate and set up TX queues
  for (int txq = 0; txq < TX_QUEUES_COUNT; txq++) {
    retval = rte_eth_tx_queue_setup(device, txq, TX_QUEUE_SIZE,
                                    rte_eth_dev_socket_id(device), NULL);
    if (retval != 0) {
      return retval;
    }
  }

  // Allocate and set up RX queues
  for (int rxq = 0; rxq < RX_QUEUES_COUNT; rxq++) {
    retval = rte_eth_rx_queue_setup(device, rxq, RX_QUEUE_SIZE,
                                    rte_eth_dev_socket_id(device),
                                    NULL, // default config
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
  for (uint16_t device = 0; device < rte_eth_dev_count(); device++) {
    if (rte_eth_dev_socket_id(device) > 0 &&
        rte_eth_dev_socket_id(device) != (int)rte_socket_id()) {
      NF_INFO("Device %" PRIu8 " is on remote NUMA node to polling thread.",
              device);
    }
  }

  if (!nf_init()) {
    rte_exit(EXIT_FAILURE, "Error initializing NF");
  }

  NF_INFO("Core %u forwarding packets.", rte_lcore_id());

#ifdef VIGOR_DEBUG_PERF
  NF_INFO("Counters: instructions, L1d, L1i, L2, L3");
  int papi_events[] = {PAPI_TOT_INS, PAPI_L1_DCM, PAPI_L1_ICM, PAPI_L2_TCM, PAPI_L3_TCM};
  #define papi_events_count sizeof(papi_events)/sizeof(papi_events[0])
  #define papi_batch_size 10000
  long long papi_values[papi_batch_size][papi_events_count];
  if (PAPI_start_counters(papi_events, papi_events_count) != PAPI_OK) {
    rte_exit(EXIT_FAILURE, "Couldn't start PAPI counters.");
  }
  uint64_t papi_counter = 0;
#endif

#if VIGOR_BATCH_SIZE == 1
  VIGOR_LOOP_BEGIN

#ifdef VIGOR_DEBUG_PERF
    PAPI_read_counters(papi_values[papi_counter], papi_events_count);
#endif

    struct rte_mbuf *mbuf;
    if (rte_eth_rx_burst(VIGOR_DEVICE, 0, &mbuf, 1) != 0) {
      uint8_t* packet = rte_pktmbuf_mtod(mbuf, uint8_t*);
      packet_state_total_length(packet, &(mbuf->pkt_len));
      uint16_t dst_device = nf_process(mbuf->port, packet, mbuf->data_len, VIGOR_NOW);
      nf_return_all_chunks(packet);

      if (dst_device == VIGOR_DEVICE) {
        rte_pktmbuf_free(mbuf);
      } else if (dst_device == FLOOD_FRAME) {
        flood(mbuf, VIGOR_DEVICE, VIGOR_DEVICES_COUNT);
      } else {
        concretize_devices(&dst_device, rte_eth_dev_count());
        if (rte_eth_tx_burst(dst_device, 0, &mbuf, 1) != 1) {
#if defined(VIGOR_ALLOW_DROPS) || defined(VIGOR_DEBUG_PERF)
          rte_pktmbuf_free(mbuf);
#else
          printf("We assume the hardware will allways accept a packet for send.\n");
          exit(1);
#endif
        }
      }

#ifdef VIGOR_DEBUG_PERF
      PAPI_read_counters(papi_values[papi_counter], papi_events_count);
      papi_counter++;
      if (papi_counter == papi_batch_size) {
        papi_counter = 0;
        for (uint64_t n = 0; n < papi_batch_size; n++) {
          for (uint64_t e = 0; e < papi_events_count; e++) {
            printf("%lld ", papi_values[n][e]);
          }
          printf("\n");
        }
      }
#endif

    }
  VIGOR_LOOP_END
#else
  if (rte_eth_dev_count() != 2) {
    printf("We assume there will be exactly 2 devices for our simple batching implementation.");
    exit(1);
  }
  NF_INFO("Running with batches, this code is unverified!");

  VIGOR_LOOP_BEGIN
    struct rte_mbuf *mbufs[VIGOR_BATCH_SIZE];
    struct rte_mbuf *mbufs_to_send[VIGOR_BATCH_SIZE];
    int mbuf_send_index = 0;
    uint16_t received_count = rte_eth_rx_burst(VIGOR_DEVICE, 0, mbufs, VIGOR_BATCH_SIZE);
    for (uint16_t n = 0; n < received_count; n++) {
      uint8_t* packet = rte_pktmbuf_mtod(mbufs[n], uint8_t*);
      packet_state_total_length(packet, &(mbufs[n]->pkt_len));
      uint16_t dst_device = nf_process(mbufs[n]->port, packet, mbufs[n]->data_len, VIGOR_NOW);
      nf_return_all_chunks(packet);

      if (dst_device == VIGOR_DEVICE) {
        rte_pktmbuf_free(mbufs[n]);
      } else { // includes flood when 2 devices, which is equivalent to just a send
        mbufs_to_send[mbuf_send_index] = mbufs[n];
        mbuf_send_index++;
      }
    }

    uint16_t sent_count = rte_eth_tx_burst(1 - VIGOR_DEVICE, 0, mbufs_to_send, mbuf_send_index);
    for (uint16_t n = sent_count; n < mbuf_send_index; n++) {
      rte_pktmbuf_free(mbufs[n]); // should not happen, but we're in the unverified case anyway
    }
  VIGOR_LOOP_END
#endif
}

// --- Main ---

int MAIN(int argc, char *argv[]) {
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

  // Initialize all devices
  for (uint16_t device = 0; device < nb_devices; device++) {
    ret = nf_init_device(device, mbuf_pool);
    if (ret == 0) {
      NF_INFO("Initialized device %" PRIu16 ".", device);
    } else {
      rte_exit(EXIT_FAILURE, "Cannot init device %" PRIu16 ", ret=%d", device,
               ret);
    }
  }

  // Run!
  // ...in single-threaded mode, that is.
  lcore_main();

  return 0;
}
