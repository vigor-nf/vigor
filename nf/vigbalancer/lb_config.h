#pragma once

#include <inttypes.h>

#include <rte_config.h>
#include <rte_ether.h>


struct lb_config {
	// Number of backends
	uint16_t backend_count;

	// MAC addresses of the devices the backends are connected to
	struct ether_addr* device_macs;

	// Size of the flow table
	uint32_t flow_capacity;

	// Expiration time of flows in seconds
	uint64_t flow_expiration_time;

  // The maximum number of backends we can ballance at the same time
  uint32_t backend_capacity;

  // The height of the consistent hashing table.
  // Bigger value induces more memory usage, but can achieve finer
  // granularity.
  uint32_t cht_height;

  // The time for which the load balancer is willing to wait hoping to get
  // another heartbeat. If no heartbeat comes for a host for this time,
  // it is considered down and removed from the pool of backends.
  uint64_t backend_expiration_time;
};


void lb_config_init(struct lb_config* config,
                    int argc, char** argv);

void lb_config_cmdline_print_usage(void);

void lb_print_config(struct lb_config* config);
