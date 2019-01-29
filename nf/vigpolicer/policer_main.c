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

int policer_expire_entries(time_t time) {
  if (time < config.burst / config.rate) return 0;

  // This is convoluted - we want to make sure the sanitization doesn't
  // extend our time_t value in 128 bits, which would confuse the validator.
  // So we "prove" by hand that it's OK...
  // We know time >= 0 since time >= config.burst / config.rate
  assert(sizeof(time_t) <= sizeof(uint64_t));
  uint64_t time_u = (uint64_t) time; // OK since assert above passed and time > 0
  uint64_t min_time_u = time_u - config.burst / config.rate; // OK because time >= config.burst / config.rate >= 0
  assert(sizeof(uint64_t) <= sizeof(time_t));
  time_t min_time = (time_t) min_time_u; // OK since the assert above passed

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

    bool fwd = false;
    if (value->bucket_size + (time - value->bucket_time) * config.rate / 1000000000 > size) {
      value->bucket_size = value->bucket_size + (time - value->bucket_time) * config.rate / 1000000000 - size;
      value->bucket_time = time;
      fwd = true;
      NF_DEBUG("  Known flow within limit. Forwarding.");
    } else {
      NF_DEBUG("  Known flow outside of limit. Dropping.");
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
    map_put(dynamic_ft.map, &key, index);
    //the other half of the key is in the map
    vector_return(dynamic_ft.keys, index, key);
    vector_return(dynamic_ft.values, index, value);

    NF_DEBUG("  New flow. Forwarding.");
    return true;
  }
}

#ifdef KLEE_VERIFICATION
struct str_field_descr dynamic_map_key_fields[] = {
  {0, sizeof(uint8_t), 4, "dst_addr"},
};

struct str_field_descr dynamic_vector_key_fields[] = {
  {0, sizeof(uint8_t), 4, "dst_addr"},
};

struct str_field_descr dynamic_vector_value_fields[] = {
  {0, sizeof(uint32_t), 0, "bucket_size"},
  {0, sizeof(uint64_t), 0, "bucket_time"},
};
#endif//KLEE_VERIFICATION

void nf_core_init(void) {
  unsigned capacity = config.dyn_capacity;
  int happy = map_allocate(ip_addr_eq, ip_addr_hash,
                           capacity, &dynamic_ft.map);
  if (!happy) rte_exit(EXIT_FAILURE, "error allocating dynamic map");
  happy = vector_allocate(sizeof(struct ether_addr), capacity,
                          init_nothing_ea,
                          &dynamic_ft.keys);
  if (!happy) rte_exit(EXIT_FAILURE, "error allocating dynamic key array");
  happy = vector_allocate(sizeof(struct DynamicValue), capacity,
                          init_nothing_dv,
                          &dynamic_ft.values);
  if (!happy) rte_exit(EXIT_FAILURE, "error allocating dynamic value array");
  happy = dchain_allocate(capacity, &dynamic_ft.heap);
  if (!happy) rte_exit(EXIT_FAILURE, "error allocating heap");

#ifdef KLEE_VERIFICATION
  map_set_layout(dynamic_ft.map, dynamic_map_key_fields,
                 sizeof(dynamic_map_key_fields)/sizeof(dynamic_map_key_fields[0]),
                 NULL, 0, "ether_addr");
  vector_set_layout(dynamic_ft.keys,
                    dynamic_vector_key_fields,
                    sizeof(dynamic_vector_key_fields)/
                    sizeof(dynamic_vector_key_fields[0]),
                    NULL, 0,
                    "ether_addr");
  vector_set_layout(dynamic_ft.values,
                    dynamic_vector_value_fields,
                    sizeof(dynamic_vector_value_fields)/
                    sizeof(dynamic_vector_value_fields[0]),
                    NULL, 0,
                    "DynamicValue");
#endif//KLEE_VERIFICATION
}

int nf_core_process(struct rte_mbuf* mbuf, uint64_t now) {
  const uint16_t in_port = mbuf->port;
//   struct ether_hdr* ether_header = nf_then_get_ether_header(mbuf->buf_addr);
  struct ether_hdr *ether_header = rte_pktmbuf_mtod(mbuf, struct ether_hdr *);

  if (!RTE_ETH_IS_IPV4_HDR(mbuf->packet_type) &&
      !(mbuf->packet_type == 0 &&
        ether_header->ether_type == rte_cpu_to_be_16(ETHER_TYPE_IPv4))) {
    NF_DEBUG("Not IPv4, dropping");
    return in_port;
  }

//   uint8_t* ip_options;
//   bool wellformed = true;
// 	struct ipv4_hdr* ipv4_header = nf_then_get_ipv4_header(mbuf->buf_addr, &ip_options, &wellformed);
//   if (!wellformed) {
// 		NF_DEBUG("Malformed IPv4, dropping");
//     return in_port;
//   }
//   assert(ipv4_header != NULL);

  if (!RTE_ETH_IS_IPV4_HDR(mbuf->packet_type) &&
      !(mbuf->packet_type == 0 &&
        ether_header->ether_type == rte_cpu_to_be_16(ETHER_TYPE_IPv4))) {
    NF_DEBUG("Not IPv4, dropping");
    return in_port; // Non IPv4 packet, ignore
  }
  struct ipv4_hdr *ipv4_header = rte_pktmbuf_mtod_offset(
      mbuf, struct ipv4_hdr *, sizeof(struct ether_hdr));

  if (ipv4_header == NULL) {
    NF_DEBUG("Not IPv4, dropping");
    return in_port; // Not IPv4 packet, ignore
  }

//   policer_expire_entries(now);

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
                             time_t time) {
  policer_loop_iteration_begin(&dynamic_ft.heap,
                              &dynamic_ft.map,
                              &dynamic_ft.keys,
                              &dynamic_ft.values,
                              config.dyn_capacity,
                              time,
                              rte_eth_dev_count());
}

void nf_add_loop_iteration_assumptions(unsigned lcore_id,
                                       time_t time) {
  policer_loop_iteration_assumptions(&dynamic_ft.heap,
                                    &dynamic_ft.map,
                                    &dynamic_ft.keys,
                                    &dynamic_ft.values,
                                    config.dyn_capacity,
                                    time);
}

void nf_loop_iteration_end(unsigned lcore_id,
                           time_t time) {
  policer_loop_iteration_end(&dynamic_ft.heap,
                            &dynamic_ft.map,
                            &dynamic_ft.keys,
                            &dynamic_ft.values,
                            config.dyn_capacity,
                            time,
                            rte_eth_dev_count());
}

#endif//KLEE_VERIFICATION
