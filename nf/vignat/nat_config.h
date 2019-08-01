#pragma once

#include <stdint.h>

#include <rte_ether.h>
#include "lib/nf_time.h"



struct nat_config {
	// "Main" LAN (i.e. internal) device, used for dumb forwarding
	uint16_t lan_main_device;

	// WAN device, i.e. external
	uint16_t wan_device;

	// External IP address
	uint32_t external_addr;

	// MAC addresses of devices
	struct ether_addr* device_macs;

	// MAC addresses of the endpoints the devices are linked to
	struct ether_addr* endpoint_macs;

	// External port at which to start allocating flows
	// i.e. ports will be allocated in [start_port, start_port + max_flows]
	uint16_t start_port;

	// Expiration time of flows in nanoseconds
	vigor_time_t expiration_time;

	// Size of the flow table
	uint32_t max_flows;
};


void nat_config_init(struct nat_config* config,
                     int argc, char** argv);

void nat_config_cmdline_print_usage(void);

void nat_print_config(struct nat_config* config);
