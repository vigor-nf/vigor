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

int nf_process(uint16_t device, uint8_t* buffer, uint16_t packet_length, vigor_time_t now) {
  lb_expire_flows(balancer, now);
  lb_expire_backends(balancer, now);

  struct rte_ether_hdr *rte_ether_header = nf_then_get_rte_ether_header(buffer);
  uint8_t *ip_options;
  struct rte_ipv4_hdr *rte_ipv4_header =
      nf_then_get_rte_ipv4_header(rte_ether_header, buffer, &ip_options);
  if (rte_ipv4_header == NULL) {
    NF_DEBUG("Malformed IPv4, dropping");
    return device;
  }

  struct tcpudp_hdr *tcpudp_header =
      nf_then_get_tcpudp_header(rte_ipv4_header, buffer);
  if (tcpudp_header == NULL) {
    NF_DEBUG("Not TCP/UDP, dropping");
    return device;
  }

  struct LoadBalancedFlow flow = { .src_ip = rte_ipv4_header->src_addr,
                                   .dst_ip = rte_ipv4_header->dst_addr,
                                   .src_port = tcpudp_header->src_port,
                                   .dst_port = tcpudp_header->dst_port,
                                   .protocol = rte_ipv4_header->next_proto_id };

  if (device != config.wan_device) {
    NF_DEBUG("Processing heartbeat, device is %" PRIu16, device);
    lb_process_heartbit(balancer, &flow, rte_ether_header->s_addr, device, now);
    return device;
  }

  struct LoadBalancedBackend backend = lb_get_backend(balancer, &flow, now,
                                                      config.wan_device);

  NF_DEBUG("Processing packet from %" PRIu16 " to %" PRIu16, device, backend.nic);
  concretize_devices(&backend.nic, rte_eth_dev_count_avail());

  if (backend.nic != config.wan_device) {
    rte_ipv4_header->dst_addr = backend.ip;
    rte_ether_header->s_addr = config.device_macs[backend.nic];
    rte_ether_header->d_addr = backend.mac;

    // Checksum
    nf_set_rte_ipv4_udptcp_checksum(rte_ipv4_header, tcpudp_header, buffer);
  }

  return backend.nic;
}
