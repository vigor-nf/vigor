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

int nf_core_process(struct rte_mbuf* mbuf, time_t now)
{
	lb_expire_flows(balancer, now);
  lb_expire_backends(balancer, now);

	struct ether_hdr* ether_header = nf_get_mbuf_ether_header(mbuf);

	struct ipv4_hdr* ipv4_header = nf_get_mbuf_ipv4_header(mbuf);
	if (ipv4_header == NULL) {
		NF_DEBUG("Not IPv4, dropping");
		return mbuf->port;
	}

	struct tcpudp_hdr* tcpudp_header = nf_get_ipv4_tcpudp_header(ipv4_header);
	if (tcpudp_header == NULL) {
		NF_DEBUG("Not TCP/UDP, dropping");
		return mbuf->port;
	}

	struct LoadBalancedFlow flow = {
		.src_ip = ipv4_header->src_addr,
		.dst_ip = ipv4_header->dst_addr,
		.src_port = tcpudp_header->src_port,
		.dst_port = tcpudp_header->dst_port,
		.protocol = ipv4_header->next_proto_id
	};

	if (mbuf->port != 0) {
    lb_process_heartbit(balancer, &flow, ether_header->s_addr, mbuf->port, now);
		return mbuf->port;
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

#ifdef KLEE_VERIFICATION
#include "lb_loop.h"

void nf_loop_iteration_begin(unsigned lcore_id,
                             time_t time) {
  lb_loop_iteration_begin(lb_get_flow_to_flow_id(balancer), lb_get_flow_heap(balancer), lb_get_flow_chain(balancer), lb_get_flow_id_to_backend_id(balancer), lb_get_backend_ips(balancer), lb_get_backends(balancer), lb_get_ip_to_backend_id(balancer), lb_get_active_backends(balancer), lb_get_cht(balancer), time, config.backend_capacity, config.flow_capacity);
}

void nf_add_loop_iteration_assumptions(unsigned lcore_id,
                                       time_t time) {
  lb_loop_iteration_assumptions(lb_get_flow_to_flow_id(balancer), lb_get_flow_heap(balancer), lb_get_flow_chain(balancer), lb_get_flow_id_to_backend_id(balancer), lb_get_backend_ips(balancer), lb_get_backends(balancer), lb_get_ip_to_backend_id(balancer), lb_get_active_backends(balancer), lb_get_cht(balancer), time, config.backend_capacity, config.flow_capacity);
}

void nf_loop_iteration_end(unsigned lcore_id,
                           time_t time) {
  lb_loop_iteration_end(lb_get_flow_to_flow_id(balancer), lb_get_flow_heap(balancer), lb_get_flow_chain(balancer), lb_get_flow_id_to_backend_id(balancer), lb_get_backend_ips(balancer), lb_get_backends(balancer), lb_get_ip_to_backend_id(balancer), lb_get_active_backends(balancer), lb_get_cht(balancer), time, config.backend_capacity, config.flow_capacity);
}
#endif

