#ifdef KLEE_VERIFICATION
#include "lib/stubs/containers/map-stub-control.h" //for map_reset
#endif//KLEE_VERIFICATION
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
#include <cmdline_parse_etheraddr.h>

#include "lib/nf_forward.h"
#include "lib/nf_util.h"
#include "lib/nf_log.h"
#include "bridge_config.h"

#include "lib/containers/double-chain.h"
#include "lib/containers/map.h"
#include "lib/containers/vector.h"
#include "lib/expirator.h"

#include "bridge_state.h"

struct bridge_config config;

struct State* mac_tables;

int bridge_expire_entries(vigor_time_t time) {
  if (time < config.expiration_time) return 0;

  // This is convoluted - we want to make sure the sanitization doesn't
  // extend our vigor_time_t value in 128 bits, which would confuse the validator.
  // So we "prove" by hand that it's OK...
  // We know time >= 0 since time >= config.expiration_time
  assert(sizeof(vigor_time_t) <= sizeof(int64_t));
  uint64_t time_u = (uint64_t) time; // OK since assert above passed and time > 0
  uint64_t min_time_u = time_u - config.expiration_time; // OK because time >= expiration_time >= 0
  assert(sizeof(int64_t) <= sizeof(vigor_time_t));
  vigor_time_t min_time = (vigor_time_t) min_time_u; // OK since the assert above passed

  return expire_items_single_map(mac_tables->dyn_heap, mac_tables->dyn_keys,
                                 mac_tables->dyn_map,
                                 min_time);
}

int bridge_get_device(struct ether_addr* dst,
                      uint16_t src_device) {
  int device = -1;
  struct StaticKey k;
  memcpy(&k.addr, dst, sizeof(struct ether_addr));
  k.device = src_device;
  int present = map_get(mac_tables->st_map,
                        &k, &device);
  if (present) {
    return device;
  }
#ifdef KLEE_VERIFICATION
  map_reset(mac_tables->dyn_map);//simplify the traces for easy validation
#endif//KLEE_VERIFICATION

  int index = -1;
  present = map_get(mac_tables->dyn_map, dst, &index);
  if (present) {
    struct DynamicValue* value = 0;
    vector_borrow(mac_tables->dyn_vals, index, (void**)&value);
    device = value->device;
    vector_return(mac_tables->dyn_vals, index, value);
    return device;
  }
  return -1;
}

void bridge_put_update_entry(struct ether_addr* src,
                             uint16_t src_device,
                             vigor_time_t time) {
  int index = -1;
  int hash = ether_addr_hash(src);
  int present = map_get(mac_tables->dyn_map, src, &index);
  if (present) {
    dchain_rejuvenate_index(mac_tables->dyn_heap, index, time);
  } else {
    int allocated = dchain_allocate_new_index(mac_tables->dyn_heap,
                                              &index,
                                              time);
    if (!allocated) {
      NF_INFO("No more space in the dynamic table");
      return;
    }
    struct ether_addr* key = 0;
    struct DynamicValue* value = 0;
    vector_borrow(mac_tables->dyn_keys, index, (void**)&key);
    vector_borrow(mac_tables->dyn_vals, index, (void**)&value);
    memcpy(key, src, sizeof(struct ether_addr));
    value->device = src_device;
    map_put(mac_tables->dyn_map, key, index);
    //the other half of the key is in the map
    vector_return(mac_tables->dyn_keys, index, key);
    vector_return(mac_tables->dyn_vals, index, value);
  }
}

bool stat_map_condition(void* key, int index) {
  return 0 <= index & index < rte_eth_dev_count();
}

bool dyn_val_condition(void* val, int index, void* state) {
  struct DynamicValue* v = val;
  return 0 <= v->device & v->device < rte_eth_dev_count();
}

// File parsing, is not really the kind of code we want to verify.
#ifdef KLEE_VERIFICATION

//TODO: this function must appear in the traces.
// let's see if we notice that it does not
void read_static_ft_from_file(struct Map* stat_map, struct Vector* stat_keys, uint32_t stat_capacity) {
}

static void read_static_ft_from_array(struct Map* stat_map, struct Vector* stat_keys, uint32_t stat_capacity) {
}

#else//KLEE_VERIFICATION

#ifndef DSOS
static void read_static_ft_from_file(struct Map* stat_map, struct Vector* stat_keys, uint32_t stat_capacity) {
  if (config.static_config_fname[0] == '\0') {
    // No static config
    return;
  }

  FILE* cfg_file = fopen(config.static_config_fname, "r");
  if (cfg_file == NULL) {
    rte_exit(EXIT_FAILURE, "Error opening the static config file: %s",
             config.static_config_fname);
  }

  unsigned number_of_lines = 0;
  char ch;
  do {
    ch = fgetc(cfg_file);
    if(ch == '\n')
      number_of_lines++;
  } while (ch != EOF);

  // Make sure the hash table is occupied only by 50%
  unsigned capacity = number_of_lines * 2;
  rewind(cfg_file);
  if (stat_capacity <= capacity) {
    rte_exit(EXIT_FAILURE, "Too many static rules (%d), max: %d",
             number_of_lines, stat_capacity/2);
  }
  int count = 0;

  while (1) {
    char mac_addr_str[20];
    char source_str[10];
    char target_str[10];
    int result = fscanf(cfg_file, "%18s", mac_addr_str);
    if (result != 1) {
      if (result == EOF) break;
      else {
        NF_INFO("Cannot read MAC address from file: %s",
                strerror(errno));
        goto finally;
      }
    }

    result = fscanf(cfg_file, "%9s", source_str);
    if (result != 1) {
      if (result == EOF) {
        NF_INFO("Incomplete config string: %s, skip", mac_addr_str);
        break;
      } else {
        NF_INFO("Cannot read the filtering target for MAC %s: %s",
                mac_addr_str, strerror(errno));
        goto finally;
      }
    }

    result = fscanf(cfg_file, "%9s", target_str);
    if (result != 1) {
      if (result == EOF) {
        NF_INFO("Incomplete config string: %s, skip", mac_addr_str);
        break;
      } else {
        NF_INFO("Cannot read the filtering target for MAC %s: %s",
                mac_addr_str, strerror(errno));
        goto finally;
      }
    }

    int device_from;
    int device_to;
    char* temp;
    struct StaticKey* key = 0;
    vector_borrow(stat_keys, count, (void**)&key);

    // Ouff... the strings are extracted, now let's parse them.
    result = cmdline_parse_etheraddr(NULL, mac_addr_str,
                                     &key->addr,
                                     sizeof(struct ether_addr));
    if (result < 0) {
      NF_INFO("Invalid MAC address: %s, skip",
              mac_addr_str);
      continue;
    }

    device_from = strtol(source_str, &temp, 10);
    if (temp == source_str || *temp != '\0') {
      NF_INFO("Non-integer value for the forwarding rule: %s (%s), skip",
              mac_addr_str, target_str);
      continue;
    }

    device_to = strtol(target_str, &temp, 10);
    if (temp == target_str || *temp != '\0') {
      NF_INFO("Non-integer value for the forwarding rule: %s (%s), skip",
              mac_addr_str, target_str);
      continue;
    }

    // Now everything is alright, we can add the entry
    key->device = device_from;
    map_put(stat_map, &key->addr, device_to);
    vector_return(stat_keys, count, key);
    ++count;
    assert(count < capacity);
  }
 finally:
  fclose(cfg_file);
}
#endif

struct {
  const char mac_addr[18];
  const int device_from;
  const int device_to;
} static_rules[] = {
  { "00:00:00:00:00:00", 0, 0 },
};

static void read_static_ft_from_array(struct Map* stat_map, struct Vector* stat_keys, uint32_t stat_capacity) {
  unsigned number_of_entries = sizeof(static_rules) / sizeof(static_rules[0]);

  // Make sure the hash table is occupied only by 50%
  unsigned capacity = number_of_entries * 2;
  if (stat_capacity <= capacity) {
    rte_exit(EXIT_FAILURE, "Too many static rules (%d), max: %d",
             number_of_entries, CAPACITY_UPPER_LIMIT/2);
  }
  int count = 0;

  for (int idx = 0; idx < number_of_entries; idx++) {
    struct StaticKey* key = 0;
    vector_borrow(stat_keys, count, (void**)&key);

    int result = cmdline_parse_etheraddr(NULL, static_rules[idx].mac_addr,
                                     &key->addr,
                                     sizeof(struct ether_addr));
    if (result < 0) {
      NF_INFO("Invalid MAC address: %s, skip",
              static_rules[idx].mac_addr);
      continue;
    }

    // Now everything is alright, we can add the entry
    key->device = static_rules[idx].device_from;
    map_put(stat_map, &key->addr, static_rules[idx].device_to);
    vector_return(stat_keys, count, key);
    ++count;
    assert(count < capacity);
  }
}

#endif//KLEE_VERIFICATION

void nf_core_init(void) {
  unsigned stat_capacity = CAPACITY_UPPER_LIMIT - 1;
  unsigned capacity = config.dyn_capacity;

  mac_tables = alloc_state(capacity, stat_capacity, rte_eth_dev_count());
  if (mac_tables == NULL) {
		rte_exit(EXIT_FAILURE, "Could not allocate mac tables");
  } else {
#ifdef DSOS
    read_static_ft_from_array(mac_tables->st_map, mac_tables->st_vec, stat_capacity);
#else
    read_static_ft_from_file(mac_tables->st_map, mac_tables->st_vec, stat_capacity);
#endif
  }
}

int nf_core_process(struct rte_mbuf* mbuf, vigor_time_t now) {
  const uint16_t in_port = mbuf->port;
  struct ether_hdr* ether_header = nf_then_get_ether_header(mbuf_pkt(mbuf));

  bridge_expire_entries(now);
  bridge_put_update_entry(&ether_header->s_addr, in_port, now);

  int forward_to = bridge_get_device(&ether_header->d_addr, in_port);

  if (forward_to == -1) {
    return FLOOD_FRAME;
  }

  if (forward_to == -2) {
    NF_DEBUG("filtered frame");
    return in_port;
  }

  return forward_to;
}

void nf_config_init(int argc, char** argv) {
  bridge_config_init(&config, argc, argv);
}

void nf_config_cmdline_print_usage(void) {
  bridge_config_cmdline_print_usage();
}

void nf_print_config() {
  bridge_print_config(&config);
}
