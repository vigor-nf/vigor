#include "config.h"
#include "nf.h"

// ===
// This file contains the parsing and displaying logic for your NF's config-
// ===

#include <getopt.h>
#include <stdlib.h>
#include <stdio.h>

#include "nf-util.h"
#include "nf-log.h"
#include "nf-parse.h"

#define PARSE_ERROR(format, ...)          \
  nf_config_usage();                      \
  fprintf(stderr, format, ##__VA_ARGS__); \
  exit(EXIT_FAILURE);

void nf_config_init(int argc, char **argv) {
  uint16_t nb_devices = rte_eth_dev_count();

  struct option long_options[] = { { "eth-dest", required_argument, NULL, 'm' },
                                   { NULL, 0, NULL, 0 } };

  config.device_macs = calloc(nb_devices, sizeof(struct rte_ether_addr));
  config.endpoint_macs = calloc(nb_devices, sizeof(struct rte_ether_addr));

  // Set the devices' own MACs
  for (uint16_t device = 0; device < nb_devices; device++) {
    rte_eth_macaddr_get(device, &(config.device_macs[device]));
  }

  int opt;
  while ((opt = getopt_long(argc, argv, "m:", long_options, NULL)) != EOF) {
    unsigned device;
    switch (opt) {
      case 'm':
        device = nf_util_parse_int(optarg, "eth-dest device", 10, ',');
        if (device >= nb_devices) {
          PARSE_ERROR("eth-dest: device %d >= nb_devices (%d)\n", device,
                      nb_devices);
        }

        optarg += 2;
        if (!nf_parse_etheraddr(optarg, &(config.endpoint_macs[device]))) {
          PARSE_ERROR("Invalid MAC address: %s\n", optarg);
        }
        break;
    }
  }

  // Reset getopt
  optind = 1;
}

void nf_config_usage(void) {
  NF_INFO("Usage:\n"
          "[DPDK EAL options] --\n"
          "\t--eth-dest <device>,<mac>: MAC address of the endpoint linked to "
          "a device.\n");
}

void nf_config_print(void) {
  NF_INFO("\n--- Config ---\n");

  uint16_t nb_devices = rte_eth_dev_count();
  for (uint16_t dev = 0; dev < nb_devices; dev++) {
    char *dev_mac_str = nf_mac_to_str(&(config.device_macs[dev]));
    char *end_mac_str = nf_mac_to_str(&(config.endpoint_macs[dev]));

    NF_INFO("Device %" PRIu16 " own-mac: %s, end-mac: %s", dev, dev_mac_str,
            end_mac_str);

    free(dev_mac_str);
    free(end_mac_str);
  }

  NF_INFO("\n--- ------ ---\n");
}
