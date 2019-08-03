#include "fw_config.h"

#include <getopt.h>
#include <stdlib.h>

// DPDK needs these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>

#include <rte_common.h>
#include <rte_ethdev.h>

#include <cmdline_parse_etheraddr.h>
#include <cmdline_parse_ipaddr.h>

#include "libvig/nf_util.h"
#include "libvig/nf_log.h"


#define PARSE_ERROR(format, ...)                  \
  fw_config_cmdline_print_usage();               \
  rte_exit(EXIT_FAILURE, format, ##__VA_ARGS__);


void fw_config_init(struct fw_config* config,
                    int argc, char** argv)
{
  uint16_t nb_devices = rte_eth_dev_count();

  struct option long_options[] = {
    {"eth-dest",        required_argument,    NULL, 'm'},
    {"expire",        required_argument,    NULL, 't'},
    {"max-flows",        required_argument,    NULL, 'f'},
    {"wan",            required_argument,    NULL, 'w'},
    {NULL,             0,            NULL,  0 }
  };

  config->device_macs = calloc(nb_devices, sizeof(struct ether_addr));
  config->endpoint_macs = calloc(nb_devices, sizeof(struct ether_addr));

  // Set the devices' own MACs
  for (uint16_t device = 0; device < nb_devices; device++) {
    rte_eth_macaddr_get(device, &(config->device_macs[device]));
  }

  int opt;
  while ((opt = getopt_long(argc, argv, "m:t:f:w:", long_options, NULL)) != EOF) {
    unsigned device;
    switch (opt) {
    case 'm':
      device = nf_util_parse_int(optarg, "eth-dest device", 10, ',');
      if (device >= nb_devices) {
        PARSE_ERROR("eth-dest: device %d >= nb_devices (%d)\n", device, nb_devices);
      }

      optarg += 2;
      if (cmdline_parse_etheraddr(NULL, optarg, &(config->endpoint_macs[device]), sizeof(int64_t)) < 0) {
        PARSE_ERROR("Invalid MAC address: %s\n", optarg);
      }
      break;

    case 't':
      config->expiration_time = nf_util_parse_int(optarg, "exp-time", 10, '\0');
      if (config->expiration_time == 0) {
        PARSE_ERROR("Expiration time must be strictly positive.\n");
      }
      break;

    case 'f':
      config->max_flows = nf_util_parse_int(optarg, "max-flows", 10, '\0');
      if (config->max_flows <= 0) {
        PARSE_ERROR("Flow table size must be strictly positive.\n");
      }
      break;

    case 'w':
      config->wan_device = nf_util_parse_int(optarg, "wan-dev", 10, '\0');
      if (config->wan_device >= nb_devices) {
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
}

void fw_config_cmdline_print_usage(void)
{
  NF_INFO("Usage:\n"
          "[DPDK EAL options] --\n"
          "\t--eth-dest <device>,<mac>: MAC address of the endpoint linked to a device.\n"
          "\t--expire <time>: flow expiration time (ns).\n"
          "\t--max-flows <n>: flow table capacity.\n"
          "\t--wan <device>: set device to be the external one.\n"
          );
}

void fw_print_config(struct fw_config* config)
{
  NF_INFO("\n--- FW Config ---\n");

  NF_INFO("WAN device: %" PRIu16, config->wan_device);

  uint16_t nb_devices = rte_eth_dev_count();
  for (uint16_t dev = 0; dev < nb_devices; dev++) {
    char* dev_mac_str = nf_mac_to_str(&(config->device_macs[dev]));
    char* end_mac_str = nf_mac_to_str(&(config->endpoint_macs[dev]));

    NF_INFO("Device %" PRIu16 " own-mac: %s, end-mac: %s",
            dev, dev_mac_str, end_mac_str);

    free(dev_mac_str);
    free(end_mac_str);
  }

  NF_INFO("Expiration time: %" PRVIGT "ns", config->expiration_time);
  NF_INFO("Max flows: %" PRIu32, config->max_flows);

  NF_INFO("\n--- --- ------ ---\n");
}
