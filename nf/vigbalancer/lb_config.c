#include <getopt.h>
#include <stdint.h>
#include <stdlib.h>

// DPDK needs these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>

#include <rte_common.h>
#include <rte_config.h>
#include <rte_ethdev.h>

#include <cmdline_parse_etheraddr.h>

#include "lb_config.h"
#include "lib/nf_util.h"
#include "lib/nf_log.h"


#define PARSE_ERROR(format, ...) \
		lb_config_cmdline_print_usage(); \
		rte_exit(EXIT_FAILURE, format, ##__VA_ARGS__);


void lb_config_init(struct lb_config* config,
                    int argc, char** argv)
{
	// Init
	struct option long_options[] = {
		{"flow-expiration",	required_argument,	NULL, 'x'},
		{"flow-capacity",	required_argument,	NULL, 'f'},
    {"backend-capacity", required_argument, NULL, 's'},
    {"cht-height", required_argument, NULL, 'h'},
    {"backend-expiration", required_argument, NULL, 't'},
		{NULL, 			0,			NULL,  0 }
	};

	int opt;
	while ((opt = getopt_long(argc, argv, "b:x:f:", long_options, NULL)) != EOF) {
		switch (opt) {
			case 'x':
				config->flow_expiration_time = nf_util_parse_int(optarg, "flow-expiration", 10, '\0');
				if (config->flow_expiration_time == 0) {
					PARSE_ERROR("Flow expiration time must be strictly positive.\n");
				}
				break;

			case 'f':
				config->flow_capacity = nf_util_parse_int(optarg, "flow-capacity", 10, '\0');
				if (config->flow_capacity <= 0) {
					PARSE_ERROR("Flow capacity must be strictly positive.\n");
				}
				break;

      case 's':
        config->backend_capacity =
          nf_util_parse_int(optarg, "backend-capacity", 10, '\0');
        if (config->flow_capacity <= 0) {
          PARSE_ERROR("Flow capacity must be strictly positive.\n");
        }
        break;

      case 'h':
        config->cht_height = nf_util_parse_int(optarg, "cht-height", 10, '\0');
        if (config->flow_capacity <= 0) {
          PARSE_ERROR("Flow capacity must be strictly positive.\n");
        }
        break;

      case 't':
        config->backend_expiration_time = nf_util_parse_int(optarg, "backend-expiration", 10, '\0');
        if (config->flow_expiration_time == 0) {
          PARSE_ERROR("Flow expiration time must be strictly positive.\n");
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
  config->device_macs = malloc(sizeof(struct ether_addr) * rte_eth_dev_count());
  for (int i = 0; i < rte_eth_dev_count(); ++i) {
    rte_eth_macaddr_get(i, &config->device_macs[i]);
  }
}

void lb_config_cmdline_print_usage(void)
{
	NF_INFO("Usage:\n"
		"[DPDK EAL options] --\n"
		"\t--backend <mac>: backend MAC address (one per backend, configured sequentially).\n"
		"\t--flow-expiration <time>: flow expiration time.\n"
		"\t--flow-capacity <n>: flow table capacity.\n"
   		"\t--backend-capacity <n>: backend table capacity.\n"
   		"\t--cht-height <n>: consistent hashing table height: bigger <n> generates more smooth distribution.\n"
   		"\t--backend-expiration <time>: backend expiration time.\n"
	);
}

void lb_print_config(struct lb_config* config)
{
	NF_INFO("\n--- LoadBalancer Config ---\n");

	for (uint16_t b = 0; b < config->backend_count; b++) {
		char* dev_mac_str = nf_mac_to_str(&(config->device_macs[b]));

		NF_INFO("Backend device %" PRIu16 " own-mac: %s", b, dev_mac_str);

		free(dev_mac_str);
	}

	NF_INFO("Flow expiration time: %" PRIu32, config->flow_expiration_time);
	NF_INFO("Flow capacity: %" PRIu32, config->flow_capacity);

	NF_INFO("\n--- --- ------ ---\n");
}
