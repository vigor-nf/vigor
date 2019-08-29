#pragma once

// ===
// This file contains your NF's configuration.
// ===

#include <rte_ether.h>

struct nf_config {
  // MAC addresses of devices
  struct ether_addr *device_macs;

  // MAC addresses of the endpoints the devices are linked to
  struct ether_addr *endpoint_macs;
};
