#include <stdlib.h>

#include "lb_config.h"
#include "lb_balancer.h"
#include "nf.h"
#include "nf-log.h"
#include "nf-util.h"

struct nf_config config;

struct LoadBalancer *balancer;

bool nf_init(void) {
  balancer = lb_allocate_balancer(
      config.flow_capacity, config.backend_capacity, config.cht_height,
      config.backend_expiration_time, config.flow_expiration_time);
  return balancer != NULL;
}

int nf_process(uint16_t device, uint8_t* buffer, uint16_t buffer_length, vigor_time_t now) {
  lb_expire_flows(balancer, now);
  lb_expire_backends(balancer, now);

  struct ether_hdr *ether_header = nf_then_get_ether_header(buffer);
  uint8_t *ip_options;
  struct ipv4_hdr *ipv4_header =
      nf_then_get_ipv4_header(ether_header, buffer, &ip_options);
  if (ipv4_header == NULL) {
    NF_DEBUG("Malformed IPv4, dropping");
    return device;
  }

  struct tcpudp_hdr *tcpudp_header =
      nf_then_get_tcpudp_header(ipv4_header, buffer);
  if (tcpudp_header == NULL) {
    NF_DEBUG("Not TCP/UDP, dropping");
    return device;
  }

  struct LoadBalancedFlow flow = { .src_ip = ipv4_header->src_addr,
                                   .dst_ip = ipv4_header->dst_addr,
                                   .src_port = tcpudp_header->src_port,
                                   .dst_port = tcpudp_header->dst_port,
                                   .protocol = ipv4_header->next_proto_id };

  if (device != config.wan_device) {
    NF_DEBUG("Processing heartbeat, device is %" PRIu16, device);
    lb_process_heartbit(balancer, &flow, ether_header->s_addr, device, now);
    return device;
  }

  struct LoadBalancedBackend backend = lb_get_backend(balancer, &flow, now,
                                                      config.wan_device);

  NF_DEBUG("Processing packet from %" PRIu16 " to %" PRIu16, device, backend.nic);
  concretize_devices(&backend.nic, rte_eth_dev_count());

  if (backend.nic != config.wan_device) {
    ipv4_header->dst_addr = backend.ip;
    ether_header->s_addr = config.device_macs[backend.nic];
    ether_header->d_addr = backend.mac;

    // Checksum
    nf_set_ipv4_udptcp_checksum(ipv4_header, tcpudp_header, buffer);
  }

  return backend.nic;
}
