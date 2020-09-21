#include "nf.h"
#include "nf-log.h"
#include "nf-util.h"

#include <inttypes.h>

#include <rte_common.h>
#include <rte_eal.h>
#include <rte_errno.h>
#include <rte_ethdev.h>
#include <rte_lcore.h>
#include <rte_mbuf.h>

#include "libvig/verified/boilerplate-util.h"
#include "libvig/verified/packet-io.h"

#ifdef KLEE_VERIFICATION
#  include "libvig/models/hardware.h"
#  include "libvig/models/verified/vigor-time-control.h"
#  include <klee/klee.h>
#endif // KLEE_VERIFICATION

// NFOS declares its own main method
#ifdef NFOS
#  define MAIN nf_main
#else // NFOS
#  define MAIN main
#endif // NFOS

// Unverified support for batching, useful for performance comparisons
#ifndef VIGOR_BATCH_SIZE
#  define VIGOR_BATCH_SIZE 1
#endif

// More elaborate loop shape with annotations for verification
#ifdef KLEE_VERIFICATION
#  define VIGOR_LOOP_BEGIN                                                        \
    unsigned _vigor_lcore_id = 0; /* no multicore support for now */              \
    vigor_time_t _vigor_start_time = start_time();                                \
    int _vigor_loop_termination = klee_int("loop_termination");                   \
    unsigned VIGOR_DEVICES_COUNT = rte_eth_dev_count_avail();                           \
    while (klee_induce_invariants() & _vigor_loop_termination) {                  \
      nf_loop_iteration_border(_vigor_lcore_id, _vigor_start_time);               \
      vigor_time_t VIGOR_NOW = current_time();                                    \
      /* concretize the device to avoid leaking symbols into DPDK */              \
      uint16_t VIGOR_DEVICE = klee_range(0, VIGOR_DEVICES_COUNT, "VIGOR_DEVICE"); \
      concretize_devices(&VIGOR_DEVICE, VIGOR_DEVICES_COUNT);                     \
      stub_hardware_receive_packet(VIGOR_DEVICE);
#  define VIGOR_LOOP_END                                                          \
      stub_hardware_reset_receive(VIGOR_DEVICE);                                  \
      nf_loop_iteration_border(_vigor_lcore_id, VIGOR_NOW);                       \
    }
#else // KLEE_VERIFICATION
#  define VIGOR_LOOP_BEGIN                                                                   \
    while (1) {                                                                              \
      vigor_time_t VIGOR_NOW = current_time();                                               \
      unsigned VIGOR_DEVICES_COUNT = rte_eth_dev_count_avail();                                    \
      for (uint16_t VIGOR_DEVICE = 0; VIGOR_DEVICE < VIGOR_DEVICES_COUNT; VIGOR_DEVICE++) {
#  define VIGOR_LOOP_END                                                                     \
      }                                                                                      \
    }
#endif // KLEE_VERIFICATION


#if VIGOR_BATCH_SIZE == 1
// Queue sizes for receiving/transmitting packets
// NOT powers of 2 so that ixgbe doesn't use vector stuff
// but they have to be multiples of 8, and at least 32,
// otherwise the driver refuses to work
static const uint16_t RX_QUEUE_SIZE = 96;
static const uint16_t TX_QUEUE_SIZE = 96;
#else
// Do the opposite: we want batching!
static const uint16_t RX_QUEUE_SIZE = 128;
static const uint16_t TX_QUEUE_SIZE = 128;
#endif

// Buffer count for mempools
static const unsigned MEMPOOL_BUFFER_COUNT = 256;

// Send the given packet to all devices except the packet's own
void flood(struct rte_mbuf* packet, uint16_t nb_devices) {
  rte_mbuf_refcnt_set(packet, nb_devices - 1);
  int total_sent = 0;
  uint16_t skip_device = packet->port;
  for (uint16_t device = 0; device < nb_devices; device++) {
    if (device != skip_device) {
      total_sent += rte_eth_tx_burst(device, 0, &packet, 1);
    }
  }
  // should not happen, but in case we couldn't transmit, ensure the packet is freed
  if (total_sent != nb_devices - 1) {
    rte_mbuf_refcnt_set(packet, 1);
    rte_pktmbuf_free(packet);
  }
}

// Initializes the given device using the given memory pool
static int nf_init_device(uint16_t device, struct rte_mempool* mbuf_pool) {
  int retval;

  // device_conf passed to rte_eth_dev_configure cannot be NULL
  struct rte_eth_conf device_conf = {0};
  //device_conf.rxmode.hw_strip_crc = 1;

  // Configure the device (1, 1 == number of RX/TX queues)
  retval = rte_eth_dev_configure(device, 1, 1, &device_conf);
  if (retval != 0) {
    return retval;
  }

  // Allocate and set up a TX queue (NULL == default config)
  retval = rte_eth_tx_queue_setup(device, 0, TX_QUEUE_SIZE,
                                  rte_eth_dev_socket_id(device), NULL);
  if (retval != 0) {
    return retval;
  }

  // Allocate and set up RX queues (NULL == default config)
  retval = rte_eth_rx_queue_setup(device, 0, RX_QUEUE_SIZE,
                                  rte_eth_dev_socket_id(device),
                                  NULL, mbuf_pool);
  if (retval != 0) {
    return retval;
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

// Main worker method (for now used on a single thread...)
static void worker_main(void) {
  if (!nf_init()) {
    rte_exit(EXIT_FAILURE, "Error initializing NF");
  }

  NF_INFO("Core %u forwarding packets.", rte_lcore_id());

#if VIGOR_BATCH_SIZE == 1
  VIGOR_LOOP_BEGIN
    struct rte_mbuf* mbuf;
    if (rte_eth_rx_burst(VIGOR_DEVICE, 0, &mbuf, 1) != 0) {
      uint8_t* data = rte_pktmbuf_mtod(mbuf, uint8_t*);
      packet_state_total_length(data, &(mbuf->pkt_len));
      uint16_t dst_device = nf_process(mbuf->port, data, mbuf->pkt_len, VIGOR_NOW);
      nf_return_all_chunks(data);

      if (dst_device == VIGOR_DEVICE) {
        rte_pktmbuf_free(mbuf);
      } else if (dst_device == FLOOD_FRAME) {
        flood(mbuf, VIGOR_DEVICES_COUNT);
      } else {
        // ensure we don't leak symbols into DPDK
        concretize_devices(&dst_device, rte_eth_dev_count_avail());
        if (rte_eth_tx_burst(dst_device, 0, &mbuf, 1) != 1) {
#ifdef VIGOR_ALLOW_DROPS
          rte_pktmbuf_free(mbuf); // OK, we're debugging
#else
          printf("We assume the hardware will allways accept a packet to transmit.\n");
          abort();
#endif
        }
      }
    }
  VIGOR_LOOP_END

#else // if VIGOR_BATCH_SIZE != 1

  if (rte_eth_dev_count() != 2) {
    printf("We assume there will be exactly 2 devices for our simple batching implementation.");
    exit(1);
  }
  NF_INFO("Running with batches, this code is unverified!");

  while(1) {
    unsigned VIGOR_DEVICES_COUNT = rte_eth_dev_count();
    for (uint16_t VIGOR_DEVICE = 0; VIGOR_DEVICE < VIGOR_DEVICES_COUNT; VIGOR_DEVICE++) {
      struct rte_mbuf* mbufs[VIGOR_BATCH_SIZE];
      uint16_t rx_count = rte_eth_rx_burst(VIGOR_DEVICE, 0, mbufs, VIGOR_BATCH_SIZE);

      struct rte_mbuf *mbufs_to_send[VIGOR_BATCH_SIZE];
      uint16_t tx_count = 0;
      for (uint16_t n = 0; n < rx_count; n++) {
        uint8_t* data = rte_pktmbuf_mtod(mbufs[n], uint8_t*);
        packet_state_total_length(data, &(mbufs[n]->pkt_len));
        vigor_time_t VIGOR_NOW = current_time();
        uint16_t dst_device = nf_process(mbufs[n]->port, data, mbufs[n]->pkt_len, VIGOR_NOW);
        nf_return_all_chunks(data);

        if (dst_device == VIGOR_DEVICE) {
          rte_pktmbuf_free(mbufs[n]);
        } else { // includes flood when 2 devices, which is equivalent to just a send
          mbufs_to_send[tx_count] = mbufs[n];
          tx_count++;
       }
     }

      uint16_t sent_count = rte_eth_tx_burst(1 - VIGOR_DEVICE, 0, mbufs_to_send, tx_count);
      for (uint16_t n = sent_count; n < tx_count; n++) {
        rte_pktmbuf_free(mbufs[n]); // should not happen, but we're in the unverified case anyway
      }
    }
  }
#endif
}


// Entry point
int MAIN(int argc, char** argv) {
  // Initialize the DPDK Environment Abstraction Layer (EAL)
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
  unsigned nb_devices = rte_eth_dev_count_avail();
  struct rte_mempool *mbuf_pool = rte_pktmbuf_pool_create(
      "MEMPOOL", // name
      MEMPOOL_BUFFER_COUNT * nb_devices, // #elements
      0, // cache size (per-core, not useful in a single-threaded app)
      0, // application private area size
      RTE_MBUF_DEFAULT_BUF_SIZE, // data buffer size
      rte_socket_id()            // socket ID
  );
  if (mbuf_pool == NULL) {
    rte_exit(EXIT_FAILURE, "Cannot create pool: %s\n", rte_strerror(rte_errno));
  }

  // Initialize all devices
  for (uint16_t device = 0; device < nb_devices; device++) {
    ret = nf_init_device(device, mbuf_pool);
    if (ret == 0) {
      NF_INFO("Initialized device %" PRIu16 ".", device);
    } else {
      rte_exit(EXIT_FAILURE, "Cannot init device %" PRIu16 ": %d", device, ret);
    }
  }

  // Run!
  worker_main();

  return 0;
}
