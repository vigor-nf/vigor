#include <getopt.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

#include "lb_config.h"
#include "nf-util.h"
#include "nf-log.h"

#define PARSE_ERROR(format, ...)          \
  nf_config_usage();                      \
  fprintf(stderr, format, ##__VA_ARGS__); \
  exit(EXIT_FAILURE);

void nf_config_init(int argc, char **argv) {
  // Init
  uint16_t nb_devices = rte_eth_dev_count_avail();

  struct option long_options[] = {
    { "flow-expiration", required_argument, NULL, 'x' },
    { "flow-capacity", required_argument, NULL, 'f' },
    { "backend-capacity", required_argument, NULL, 's' },
    { "cht-height", required_argument, NULL, 'h' },
    { "backend-expiration", required_argument, NULL, 't' },
    { "wan", required_argument, NULL, 'w' },
    { NULL, 0, NULL, 0 }
  };

  int opt;
  while ((opt = getopt_long(argc, argv, "b:x:f:", long_options, NULL)) != EOF) {
    switch (opt) {
      case 'x':
        config.flow_expiration_time =
            nf_util_parse_int(optarg, "flow-expiration", 10, '\0');
        if (config.flow_expiration_time == 0) {
          PARSE_ERROR("Flow expiration time must be strictly positive.\n");
        }
        break;

      case 'f':
        config.flow_capacity =
            nf_util_parse_int(optarg, "flow-capacity", 10, '\0');
        if (config.flow_capacity <= 0) {
          PARSE_ERROR("Flow capacity must be strictly positive.\n");
        }
        break;

      case 's':
        config.backend_capacity =
            nf_util_parse_int(optarg, "backend-capacity", 10, '\0');
        if (config.backend_capacity <= 0) {
          PARSE_ERROR("Backend capacity must be strictly positive.\n");
        }
        break;

      case 'h':
        config.cht_height = nf_util_parse_int(optarg, "cht-height", 10, '\0');
        if (config.cht_height <= 0) {
          PARSE_ERROR("CHT height must be strictly positive.\n");
        }
        break;

      case 't':
        config.backend_expiration_time =
            nf_util_parse_int(optarg, "backend-expiration", 10, '\0');
        if (config.backend_expiration_time == 0) {
          PARSE_ERROR("Backend expiration time must be strictly positive.\n");
        }
        break;
      case 'w':
        config.wan_device = nf_util_parse_int(optarg, "wan-dev", 10, '\0');
        if (config.wan_device >= nb_devices) {
          PARSE_ERROR("WAN device does not exist.\n");
        }
        break;

      default:
        PARSE_ERROR("Unknown option.\n");
        break;
    }
  }

  // Reset getopt
  optind = 1;

  // Fill in the mac addresses
  config.device_macs = malloc(sizeof(struct rte_ether_addr) * rte_eth_dev_count_avail());
  for (int i = 0; i < rte_eth_dev_count_avail(); ++i) {
    rte_eth_macaddr_get(i, &config.device_macs[i]);
  }
}

void nf_config_usage(void) {
  NF_INFO("Usage:\n"
          "[DPDK EAL options] --\n"
          "\t--flow-expiration <time>: flow expiration time (us).\n"
          "\t--flow-capacity <n>: flow table capacity.\n"
          "\t--backend-capacity <n>: backend table capacity.\n"
          "\t--cht-height <n>: consistent hashing table height: bigger <n> "
          "generates more smooth distribution.\n"
          "\t--backend-expiration <time>: backend expiration time (us).\n"
          "\t--wan <device>: set device to be the external one.\n");
}

void nf_config_print(void) {
// FIXME why are we giving 20 backends and 3 devs for verif when the config
// assumes #backends == #devs?
#ifndef KLEE_VERIFICATION
  NF_INFO("\n--- LoadBalancer Config ---\n");

  NF_INFO("WAN device: %" PRIu16, config.wan_device);

  for (uint16_t b = 0; b < config.backend_count; b++) {
    char *dev_mac_str = nf_mac_to_str(&(config.device_macs[b]));

    NF_INFO("Backend device %" PRIu16 " own-mac: %s", b, dev_mac_str);

    free(dev_mac_str);
  }

  NF_INFO("Flow expiration time: %" PRIu32 "us", config.flow_expiration_time);
  NF_INFO("Flow capacity: %" PRIu32, config.flow_capacity);
  NF_INFO("Backend expiration time: %" PRIu32 "us",
          config.backend_expiration_time);
  NF_INFO("Backend capacity: %" PRIu32, config.backend_capacity);

  NF_INFO("\n--- --- ------ ---\n");
#endif
}
