#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#include "nf.h"
#include "nf-util.h"
#include "nf-log.h"
#include "policer_config.h"
#include "state.h"

#include "libvig/verified/double-chain.h"
#include "libvig/verified/map.h"
#include "libvig/verified/vector.h"
#include "libvig/verified/expirator.h"

struct nf_config config;

struct State *dynamic_ft;

int policer_expire_entries(vigor_time_t time) {
  assert(time >= 0); // we don't support the past
  vigor_time_t exp_time =
      VIGOR_TIME_SECONDS_MULTIPLIER * config.burst / config.rate;
  uint64_t time_u = (uint64_t)time;
  // OK because time >= config.burst / config.rate >= 0
  vigor_time_t min_time = time_u - exp_time;

  return expire_items_single_map(dynamic_ft->dyn_heap, dynamic_ft->dyn_keys,
                                 dynamic_ft->dyn_map, min_time);
}

bool policer_check_tb(uint32_t dst, uint16_t size, vigor_time_t time) {
  int index = -1;
  int present = map_get(dynamic_ft->dyn_map, &dst, &index);
  if (present) {
    dchain_rejuvenate_index(dynamic_ft->dyn_heap, index, time);

    struct DynamicValue *value = 0;
    vector_borrow(dynamic_ft->dyn_vals, index, (void **)&value);

    assert(0 <= time);
    uint64_t time_u = (uint64_t)time;
    assert(sizeof(vigor_time_t) == sizeof(int64_t));
    assert(value->bucket_time >= 0);
    assert(value->bucket_time <= time_u);
    uint64_t time_diff = time_u - value->bucket_time;
    if (time_diff <
        config.burst * VIGOR_TIME_SECONDS_MULTIPLIER / config.rate) {
      uint64_t added_tokens =
          time_diff * config.rate / VIGOR_TIME_SECONDS_MULTIPLIER;
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wtautological-compare"
      vigor_note(0 <= time_diff * config.rate / VIGOR_TIME_SECONDS_MULTIPLIER);
#pragma GCC diagnostic pop
      assert(value->bucket_size <= config.burst);
      value->bucket_size += added_tokens;
      if (value->bucket_size > config.burst) {
        value->bucket_size = config.burst;
      }
    } else {
      value->bucket_size = config.burst;
    }
    value->bucket_time = time_u;

    bool fwd = false;
    if (value->bucket_size > size) {
      value->bucket_size -= size;
      fwd = true;
    }

    vector_return(dynamic_ft->dyn_vals, index, value);

    return fwd;
  } else {
    if (size > config.burst) {
      NF_DEBUG("  Unknown flow with packet larger than burst size. Dropping.");
      return false;
    }

    int allocated =
        dchain_allocate_new_index(dynamic_ft->dyn_heap, &index, time);
    if (!allocated) {
      NF_DEBUG("No more space in the policer table");
      return false;
    }
    uint32_t *key;
    struct DynamicValue *value = 0;
    vector_borrow(dynamic_ft->dyn_keys, index, (void **)&key);
    vector_borrow(dynamic_ft->dyn_vals, index, (void **)&value);
    *key = dst;
    value->bucket_size = config.burst - size;
    value->bucket_time = time;
    map_put(dynamic_ft->dyn_map, key, index);
    // the other half of the key is in the map
    vector_return(dynamic_ft->dyn_keys, index, key);
    vector_return(dynamic_ft->dyn_vals, index, value);

    NF_DEBUG("  New flow. Forwarding.");
    return true;
  }
}

bool nf_init(void) {
  unsigned capacity = config.dyn_capacity;
  dynamic_ft = alloc_state(capacity, rte_eth_dev_count_avail());
  return dynamic_ft != NULL;
}

int nf_process(uint16_t device, uint8_t* buffer, uint16_t packet_length, vigor_time_t now) {
  NF_DEBUG("Received packet");
  struct rte_ether_hdr *rte_ether_header = nf_then_get_rte_ether_header(buffer);

  uint8_t *ip_options;
  struct rte_ipv4_hdr *rte_ipv4_header =
      nf_then_get_rte_ipv4_header(rte_ether_header, buffer, &ip_options);
  if (rte_ipv4_header == NULL) {
    NF_DEBUG("Not IPv4, dropping");
    return device;
  }

  policer_expire_entries(now);

  if (device == config.lan_device) {
    // Simply forward outgoing packets.
    NF_DEBUG("Outgoing packet. Not policing.");
    return config.wan_device;
  } else if (device == config.wan_device) {
    // Police incoming packets.
    bool fwd = policer_check_tb(rte_ipv4_header->dst_addr, packet_length, now);

    if (fwd) {
      NF_DEBUG("Incoming packet within policed rate. Forwarding.");
      return config.lan_device;
    } else {
      NF_DEBUG("Incoming packet outside of policed rate. Dropping.");
      return config.wan_device;
    }
  } else {
    // Drop any other packets.
    NF_DEBUG("Unknown port. Dropping.");
    return device;
  }
}
