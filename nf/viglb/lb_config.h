#pragma once

#include <inttypes.h>

#include <rte_config.h>
#include <rte_ether.h>


struct lb_config {
	// Internal device
	uint16_t device_int;

	// External device
	uint16_t device_ext;

	// MAC addresses of devices
	struct ether_addr device_macs[RTE_MAX_ETHPORTS];

	// MAC addresses of the endpoints the devices are linked to
	struct ether_addr endpoint_macs[RTE_MAX_ETHPORTS];

	// Port at which to start allocating flows
	// i.e. ports will be allocated in [start_port, start_port + max_flows]
	uint16_t start_port;

	// Size of the flow table
	uint32_t max_flows;

	// Expiration time of flows in seconds
	uint32_t expiration_time;

	// Number of backend servers
	uint16_t backends_count;

	// Backend IPs
	uint32_t* backends;
};


void lb_config_init(struct lb_config* config,
                    int argc, char** argv);

void lb_config_cmdline_print_usage(void);

void lb_print_config(struct lb_config* config);
