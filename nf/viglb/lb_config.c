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
	struct option long_options[] = {
		{"backend",		required_argument,	NULL, 'b'},
		{"flow-expiration",	required_argument,	NULL, 'x'},
		{"flow-capacity",	required_argument,	NULL, 'f'},
		{NULL, 			0,			NULL,  0 }
	};

	int opt;
	while ((opt = getopt_long(argc, argv, "b:x:f:", long_options, NULL)) != EOF) {
		unsigned device;
		switch (opt) {
			case 'b':
				config->backend_count++;
				if (config->backend_count == UINT16_MAX) {
					PARSE_ERROR("Too many backends.\n");
				}

				if (config->backend_count == 1) {
					config->device_macs = malloc(sizeof(struct ether_addr));
					config->backend_macs = malloc(sizeof(struct ether_addr));
				} else {
					config->device_macs = realloc(config->device_macs, config->backend_count * sizeof(struct ether_addr));
					config->backend_macs = realloc(config->backend_macs, config->backend_count * sizeof(struct ether_addr));
				}

				// Own MAC is obtained from the device itself
				rte_eth_macaddr_get(device, &(config->device_macs[device]));

				if (cmdline_parse_etheraddr(NULL, optarg, &(config->backend_macs[device]), sizeof(struct ether_addr)) < 0) {
					PARSE_ERROR("Invalid MAC address: %s\n", optarg);
				}
				break;

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

			default:
				PARSE_ERROR("Unknown option.\n");
				break;
		}
	}

	// Reset getopt
	optind = 1;
}

void lb_config_cmdline_print_usage(void)
{
	NF_INFO("Usage:\n"
		"[DPDK EAL options] --\n"
		"\t--backend <mac>: backend MAC address (one per backend, configured sequentially).\n"
		"\t--flow-expiration <time>: flow expiration time.\n"
		"\t--flow-capacity <n>: flow table capacity.\n"
	);
}

void lb_print_config(struct lb_config* config)
{
	NF_INFO("\n--- LoadBalancer Config ---\n");

	uint16_t nb_devices = rte_eth_dev_count();
	for (uint16_t dev = 0; dev < nb_devices; dev++) {
		char* dev_mac_str = nf_mac_to_str(&(config->device_macs[dev]));
		char* end_mac_str = nf_mac_to_str(&(config->backend_macs[dev]));

		NF_INFO("Device %" PRIu16 " own-mac: %s, backend-mac: %s", dev, dev_mac_str, end_mac_str);

		free(dev_mac_str);
		free(end_mac_str);
	}

	NF_INFO("Flow expiration time: %" PRIu32, config->flow_expiration_time);
	NF_INFO("Flow capacity: %" PRIu32, config->flow_capacity);

	NF_INFO("\n--- --- ------ ---\n");
}
