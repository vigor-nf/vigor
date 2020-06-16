#include "bridge_config.h"

#include <getopt.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include <rte_ethdev.h>

#include "nf.h"
#include "nf-util.h"
#include "nf-log.h"

const uint32_t DEFAULT_EXP_TIME = 300000000; // microseconds
const uint32_t DEFAULT_CAPACITY = 128;       // MAC addresses

#define PARSE_ERROR(format, ...)          \
  nf_config_usage();                      \
  fprintf(stderr, format, ##__VA_ARGS__); \
  exit(EXIT_FAILURE);

void nf_config_init(int argc, char **argv) {
  // Set the default values
  config.expiration_time = DEFAULT_EXP_TIME; // seconds
  config.dyn_capacity = DEFAULT_CAPACITY;    // MAC addresses
  config.static_config_fname[0] = '\0'; // no static filtering configuration

  unsigned nb_devices = rte_eth_dev_count_avail();

  struct option long_options[] = { { "expire", required_argument, NULL, 't' },
                                   { "capacity", required_argument, NULL, 'c' },
                                   { "config", required_argument, NULL, 'f' },
                                   { NULL, 0, NULL, 0 } };

  int opt;
  while ((opt = getopt_long(argc, argv, "t:c:f:", long_options, NULL)) != EOF) {
    unsigned device;
    switch (opt) {
      case 't':
        config.expiration_time =
            nf_util_parse_int(optarg, "exp-time", 10, '\0');
        if (config.expiration_time <= 0) {
          PARSE_ERROR("Expiration time must be strictly positive.\n");
        }
        break;

      case 'c':
        config.dyn_capacity = nf_util_parse_int(optarg, "capacity", 10, '\0');
        if (config.dyn_capacity <= 0) {
          PARSE_ERROR("Flow table size must be strictly positive.\n");
        }
        break;

      case 'f':
        strncpy(config.static_config_fname, optarg, CONFIG_FNAME_LEN - 1);
        config.static_config_fname[CONFIG_FNAME_LEN - 1] = '\0';
        break;

      default:
        PARSE_ERROR("Unknown option %c", opt);
    }
  }

  // Reset getopt
  optind = 1;
}

void nf_config_usage(void) {
  NF_INFO("Usage:\n"
          "[DPDK EAL options] --\n"
          "\t--expire <time>: flow expiration time (us), default: %" PRIu32
          ".\n"
          "\t--capacity <n>: dynamic mac learning table capacity,"
          " default: %" PRIu32 ".\n"
          "\t--config <fname>: static filtering table configuration file.\n",
          DEFAULT_EXP_TIME, DEFAULT_CAPACITY);
}

void nf_config_print(void) {
  NF_INFO("\n--- Bridge Config ---\n");

  NF_INFO("Expiration time: %" PRIu32 "us", config.expiration_time);
  NF_INFO("Capacity: %" PRIu16, config.dyn_capacity);
  NF_INFO("Static configuration file: %s", config.static_config_fname);

  NF_INFO("\n--- ------ ------ ---\n");
}
