#ifdef KLEE_VERIFICATION
#  include <klee/klee.h>
#  include "lib/stubs/containers/map-stub-control.h"
#  include "lib/stubs/containers/double-chain-stub-control.h"
#  include "lib/stubs/containers/vector-stub-control.h"
#  include "policer_loop.h"
#endif //KLEE_VERIFICATION

#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
// DPDK uses these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>
#include <unistd.h>
#include <rte_common.h>
#include <rte_ethdev.h>
#include <rte_mbuf.h>
#include <rte_byteorder.h>

#include "lib/nf_forward.h"
#include "lib/nf_util.h"
#include "lib/nf_log.h"
#include "policer_config.h"
#include "policer_data.h"

#include "lib/containers/double-chain.h"
#include "lib/containers/map.h"
#include "lib/containers/vector.h"
#include "lib/expirator.h"

struct policer_config config;

struct DynamicFilterTable dynamic_ft;

int policer_expire_entries(uint64_t time) {
  if (time < config.burst * 1000000000l / config.rate) return 0;

  // This is convoluted - we want to make sure the sanitization doesn't
  // extend our vigor_time_t value in 128 bits, which would confuse the validator.
  // So we "prove" by hand that it's OK...
  // We know time >= 0 since time >= config.burst / config.rate
//   assert(sizeof(vigor_time_t) <= sizeof(int64_t));
//   assert(sizeof(int64_t) <= sizeof(vigor_time_t));
  uint64_t min_time = time - config.burst * 1000000000l / config.rate; // OK because time >= config.burst / config.rate >= 0

  return expire_items_single_map(dynamic_ft.heap, dynamic_ft.keys,
                                 dynamic_ft.map,
                                 min_time);
}

bool policer_check_tb(uint32_t dst, uint16_t size, uint64_t time) {
  int index = -1;
  int present = map_get(dynamic_ft.map, &dst, &index);
  if (present) {
    dchain_rejuvenate_index(dynamic_ft.heap, index, time);

    struct DynamicValue* value = 0;
    vector_borrow(dynamic_ft.values, index, (void**)&value);

    value->bucket_size += (time - value->bucket_time) * config.rate / 1000000000;
    if (value->bucket_size > config.burst) {
      value->bucket_size = config.burst;
    }
    value->bucket_time = time;

    bool fwd = false;
    if (value->bucket_size > size) {
      value->bucket_size -= size;
      fwd = true;
    }

    vector_return(dynamic_ft.values, index, value);

    return fwd;
  } else {
    if (size > config.burst) {
      NF_DEBUG("  Unknown flow with packet larger than burst size. Dropping.");
      return false;
    }

    int allocated = dchain_allocate_new_index(dynamic_ft.heap,
                                              &index,
                                              time);
    if (!allocated) {
      NF_INFO("No more space in the policer table");
      return false;
    }
    uint32_t *key;
    struct DynamicValue* value = 0;
    vector_borrow(dynamic_ft.keys, index, (void**)&key);
    vector_borrow(dynamic_ft.values, index, (void**)&value);
    *key = dst;
    value->bucket_size = config.burst - size;
    value->bucket_time = time;
    map_put(dynamic_ft.map, key, index);
    //the other half of the key is in the map
    vector_return(dynamic_ft.keys, index, key);
    vector_return(dynamic_ft.values, index, value);

    NF_DEBUG("  New flow. Forwarding.");
    return true;
  }
}

void nf_core_init(void) {
  unsigned capacity = config.dyn_capacity;
  int happy = map_allocate(ip_addr_eq, ip_addr_hash,
                           capacity, &dynamic_ft.map);
  if (!happy) rte_exit(EXIT_FAILURE, "error allocating dynamic map");
  happy = vector_allocate(sizeof(struct ip_addr), capacity,
                          ip_addr_allocate,
                          &dynamic_ft.keys);
  if (!happy) rte_exit(EXIT_FAILURE, "error allocating dynamic key array");
  happy = vector_allocate(sizeof(struct DynamicValue), capacity,
                          DynamicValue_allocate,
                          &dynamic_ft.values);
  if (!happy) rte_exit(EXIT_FAILURE, "error allocating dynamic value array");
  happy = dchain_allocate(capacity, &dynamic_ft.heap);
  if (!happy) rte_exit(EXIT_FAILURE, "error allocating heap");

#ifdef KLEE_VERIFICATION
  map_set_layout(dynamic_ft.map, ip_addr_descrs,
                 sizeof(ip_addr_descrs)/sizeof(ip_addr_descrs[0]),
                 NULL, 0, "ip_addr");
  vector_set_layout(dynamic_ft.keys,
                    ip_addr_descrs,
                    sizeof(ip_addr_descrs)/
                    sizeof(ip_addr_descrs[0]),
                    NULL, 0,
                    "ip_addr");
  vector_set_layout(dynamic_ft.values,
                    DynamicValue_descrs,
                    sizeof(DynamicValue_descrs)/
                    sizeof(DynamicValue_descrs[0]),
                    NULL, 0,
                    "DynamicValue");
#endif//KLEE_VERIFICATION
}

int nf_core_process(struct rte_mbuf* mbuf, vigor_time_t now) {
  const uint16_t in_port = mbuf->port;
  struct ether_hdr* ether_header = nf_then_get_ether_header(mbuf->buf_addr);

  if (!RTE_ETH_IS_IPV4_HDR(mbuf->packet_type) &&
      !(mbuf->packet_type == 0 &&
        ether_header->ether_type == rte_cpu_to_be_16(ETHER_TYPE_IPv4))) {
    NF_DEBUG("Not IPv4, dropping");
    return in_port;
  }

  uint8_t* ip_options;
  bool wellformed = true;
	struct ipv4_hdr* ipv4_header = nf_then_get_ipv4_header(mbuf->buf_addr, &ip_options, &wellformed);
  if (!wellformed) {
		NF_DEBUG("Malformed IPv4, dropping");
    return in_port;
  }
  assert(ipv4_header != NULL);

  policer_expire_entries(now);

  if (in_port == config.lan_device) {
    // Simply forward outgoing packets.
    NF_INFO("Outgoing packet. Not policing.");
    return config.wan_device;
  } else if (in_port == config.wan_device) {
    // Police incoming packets.
    bool fwd = policer_check_tb(ipv4_header->dst_addr, mbuf->pkt_len, now);

    if (fwd) {
      NF_INFO("Incoming packet within policed rate. Forwarding.");
      return config.lan_device;
    } else {
      NF_INFO("Incoming packet outside of policed rate. Dropping.");
      return config.wan_device;
    }
  } else {
    // Drop any other packets.
    NF_INFO("Unknown port. Dropping.");
    return in_port;
  }
}

void nf_config_init(int argc, char** argv) {
  policer_config_init(&config, argc, argv);
}

void nf_config_cmdline_print_usage(void) {
  policer_config_cmdline_print_usage();
}

void nf_print_config() {
  policer_print_config(&config);
}

#ifdef KLEE_VERIFICATION

void nf_loop_iteration_begin(unsigned lcore_id,
                             vigor_time_t time) {
  policer_loop_iteration_begin(&dynamic_ft.heap,
                              &dynamic_ft.map,
                              &dynamic_ft.keys,
                              &dynamic_ft.values,
                              config.dyn_capacity,
                              time,
                              rte_eth_dev_count());
}

void nf_add_loop_iteration_assumptions(unsigned lcore_id,
                                       vigor_time_t time) {
  policer_loop_iteration_assumptions(&dynamic_ft.heap,
                                    &dynamic_ft.map,
                                    &dynamic_ft.keys,
                                    &dynamic_ft.values,
                                    config.dyn_capacity,
                                    time);
}

void nf_loop_iteration_end(unsigned lcore_id,
                           vigor_time_t time) {
  policer_loop_iteration_end(&dynamic_ft.heap,
                            &dynamic_ft.map,
                            &dynamic_ft.keys,
                            &dynamic_ft.values,
                            config.dyn_capacity,
                            time,
                            rte_eth_dev_count());
}

#endif//KLEE_VERIFICATION
