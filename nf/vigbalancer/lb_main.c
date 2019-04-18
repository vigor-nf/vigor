// DPDK requires these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>
#include <unistd.h>

#include <stdlib.h>

#include <rte_common.h>
#include <rte_ethdev.h>
#include <rte_ether.h>
#include <rte_ip.h>
#include <rte_mbuf.h>

#include "lb_config.h"
#include "lb_balancer.h"
#include "lib/nf_forward.h"
#include "lib/nf_log.h"
#include "lib/nf_util.h"

struct lb_config config;
struct LoadBalancer* balancer;

void nf_core_init()
{
	balancer = lb_allocate_balancer(config.flow_capacity, config.backend_capacity,
                                  config.cht_height, config.backend_expiration_time,
                                  config.flow_expiration_time);
	if (balancer == NULL) {
		rte_exit(EXIT_FAILURE, "Could not allocate balancer");
	}
}

int nf_core_process(struct rte_mbuf* mbuf, vigor_time_t now)
{
	lb_expire_flows(balancer, now);
  lb_expire_backends(balancer, now);

  const int in_port = mbuf->port;

	struct ether_hdr* ether_header = nf_then_get_ether_header(mbuf_pkt(mbuf));

  if (!RTE_ETH_IS_IPV4_HDR(mbuf->packet_type)) {
		NF_DEBUG("Not IPv4, dropping");
		return in_port;
  }
  uint8_t* ip_options;
  bool wellformed = true;
	struct ipv4_hdr* ipv4_header = nf_then_get_ipv4_header(mbuf_pkt(mbuf), &ip_options, &wellformed);
  if (!wellformed) {
		NF_DEBUG("Malformed IPv4, dropping");
		return in_port;
  }
  assert(ipv4_header != NULL);

  if (!nf_has_tcpudp_header(ipv4_header) ||
      packet_get_unread_length(mbuf_pkt(mbuf)) < sizeof(struct tcpudp_hdr)) {
		NF_DEBUG("Not TCP/UDP, dropping");
		return in_port;
	}
	struct tcpudp_hdr* tcpudp_header = nf_then_get_tcpudp_header(mbuf_pkt(mbuf));
  assert(tcpudp_header != NULL);

	struct LoadBalancedFlow flow = {
		.src_ip = ipv4_header->src_addr,
		.dst_ip = ipv4_header->dst_addr,
		.src_port = tcpudp_header->src_port,
		.dst_port = tcpudp_header->dst_port,
		.protocol = ipv4_header->next_proto_id
	};

	if (in_port != 0) {
    lb_process_heartbit(balancer, &flow, ether_header->s_addr, in_port, now);
		return in_port;
	}


	struct LoadBalancedBackend backend = lb_get_backend(balancer, &flow, now);

  if (backend.nic != 0) { // If not dropped
    ipv4_header->dst_addr = backend.ip;
    ether_header->s_addr = config.device_macs[backend.nic];
    ether_header->d_addr = backend.mac;
  }

	return backend.nic;
}


void nf_config_init(int argc, char** argv) {
  lb_config_init(&config, argc, argv);
}

void nf_config_cmdline_print_usage(void) {
  lb_config_cmdline_print_usage();
}

void nf_print_config() {
  lb_print_config(&config);
}


