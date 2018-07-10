#pragma once

#include <inttypes.h>

#include <rte_config.h>
#include <rte_ether.h>


struct lb_config {
	// Number of backends
	uint16_t backend_count;

	// MAC addresses of the devices the backends are connected to
	struct ether_addr* device_macs;

	// MAC addresses of the backends
	struct ether_addr* backend_macs;

	// Size of the flow table
	uint32_t flow_count;

	// Expiration time of flows in seconds
	uint32_t flow_expiration_time;
};


void lb_config_init(struct lb_config* config,
                    int argc, char** argv);

void lb_config_cmdline_print_usage(void);

void lb_print_config(struct lb_config* config);
