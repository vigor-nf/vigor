#include <getopt.h>
#include <inttypes.h>
#include <stdlib.h>

// DPDK needs these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>

#include <rte_common.h>
#include <rte_config.h>
#include <rte_ethdev.h>

#include <cmdline_parse_etheraddr.h>
#include <cmdline_parse_ipaddr.h>

#include "lb_config.h"
#include "nf_util.h"
#include "nf_log.h"


#define PARSE_ERROR(format, ...) \
		lb_config_cmdline_print_usage(); \
		rte_exit(EXIT_FAILURE, format, ##__VA_ARGS__);


void lb_config_init(struct lb_config* config,
                    int argc, char** argv)
{
	uint16_t nb_devices = rte_eth_dev_count();

	struct option long_options[] = {
		{"dev-ext",		required_argument,	NULL, 'e'},
		{"dev-int",		required_argument,	NULL, 'i'},
		{"expire",		required_argument,	NULL, 'x'},
		{"starting-port",	required_argument,	NULL, 's'},
		{"eth-dest",		required_argument,	NULL, 'd'},
		{"max-flows",		required_argument,	NULL, 'f'},
		{"backend",		required_argument,	NULL, 'b'},
		{NULL, 			0,			NULL,  0 }
	};

	// Set the devices' own MACs
	for (uint16_t device = 0; device < nb_devices; device++) {
		rte_eth_macaddr_get(device, &(config->device_macs[device]));
	}

	int opt;
	while ((opt = getopt_long(argc, argv, "e:i:x:s:d:f:b:", long_options, NULL)) != EOF) {
		unsigned device;
		switch (opt) {
			case 'e':
				config->device_ext = nf_util_parse_int(optarg, "dev-ext", 10, '\0');
				if (config->device_ext >= nb_devices) {
					PARSE_ERROR("External device does not exist.\n");
				}
				break;

			case 'i':
				config->device_int = nf_util_parse_int(optarg, "dev-int", 10, '\0');
				if (config->device_int >= nb_devices) {
					PARSE_ERROR("Internal device does not exist.\n");
				}
				break;

			case 'x':
				config->expiration_time = nf_util_parse_int(optarg, "exp-time", 10, '\0');
				if (config->expiration_time == 0) {
					PARSE_ERROR("Expiration time must be strictly positive.\n");
				}
				break;

			case 's':
				config->start_port = nf_util_parse_int(optarg, "start-port", 10, '\0');
				break;

			case 'd':
				device = nf_util_parse_int(optarg, "eth-dest device", 10, ',');
				if (device >= nb_devices) {
					PARSE_ERROR("eth-dest: device %d >= nb_devices (%d)\n", device, nb_devices);
				}

				optarg += 2;
				if (cmdline_parse_etheraddr(NULL, optarg, &(config->endpoint_macs[device]), sizeof(int64_t)) < 0) {
					PARSE_ERROR("Invalid MAC address: %s\n", optarg);
				}
				break;

			case 'f':
				config->max_flows = nf_util_parse_int(optarg, "max-flows", 10, '\0');
				if (config->max_flows <= 0) {
					PARSE_ERROR("Flow table size must be strictly positive.\n");
				}
				break;

			case 'b':
				struct cmdline_token_ipaddr tk;
				tk.ipaddr_data.flags = CMDLINE_IPADDR_V4;

				struct cmdline_ipaddr res;
				if (cmdline_parse_ipaddr((cmdline_parse_token_hdr_t*) &tk, optarg, &res, sizeof(res)) < 0) {
					PARSE_ERROR("Invalid backend IP address: %s\n", optarg);
				}

				config->backend_count++;

				if (config->backend_count == 1) {
					config->backends = malloc(sizeof(int32_t));
				} else {
					config->backends = realloc(config->backends, config->backend_count * sizeof(int32_t));
				}

				config->backends[config->backend_count - 1] = res.addr.ipv4.s_addr;
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
		"\t--dev-ext <device>: set device to be the external device.\n"
		"\t--dev-int <device>: set device to be the internal device.\n"
		"\t--expire <time>: flow expiration time.\n"
		"\t--starting-port <n>: start of the port range for external ports.\n"
		"\t--eth-dest <device>,<mac>: MAC address of the endpoint linked to a device.\n"
		"\t--max-flows <n>: flow table capacity.\n"
		"\t--backend <ip>: backend IP address (one per backend).\n"
	);
}

void lb_print_config(struct lb_config* config)
{
	NF_INFO("\n--- LoadBalancer Config ---\n");

	NF_INFO("External device: %" PRIu16, config->device_int);
	NF_INFO("Internal device: %" PRIu16, config->device_ext);

	for (int n = 0; n < config->backend_count; n++) {
		char* ip_str = nf_ipv4_to_str(config->backends[n]);
		NF_INFO("Backend: %s", ext_ip_str);
		free(ip_str);
	}

	uint16_t nb_devices = rte_eth_dev_count();
	for (uint16_t dev = 0; dev < nb_devices; dev++) {
		char* dev_mac_str = nf_mac_to_str(&(config->device_macs[dev]));
		char* end_mac_str = nf_mac_to_str(&(config->endpoint_macs[dev]));

		NF_INFO("Device %" PRIu16 " own-mac: %s, end-mac: %s", dev, dev_mac_str, end_mac_str);

		free(dev_mac_str);
		free(end_mac_str);
	}

	NF_INFO("Starting port: %" PRIu16, config->start_port);
	NF_INFO("Expiration time: %" PRIu32, config->expiration_time);
	NF_INFO("Max flows: %" PRIu32, config->max_flows);

	NF_INFO("\n--- --- ------ ---\n");
}
