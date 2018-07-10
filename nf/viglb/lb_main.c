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
	balancer = lb_allocate_balancer(config.flow_capacity, config.flow_expiration_time, config.backend_count);
	if (balancer == NULL) {
		rte_exit(EXIT_FAILURE, "Could not allocate balancer");
	}
}

int nf_core_process(struct rte_mbuf* mbuf, time_t now)
{
	lb_expire_flows(balancer, now);

	if (mbuf->port != 0) {
		NF_DEBUG("Wrong device, dropping");
		return mbuf->port;
	}

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
		.src_port = tcpudp_header->src_port,
		.dst_port = tcpudp_header->dst_port,
		.protocol = ipv4_header->next_proto_id
	};

	uint16_t backend = lb_get_backend(balancer, &flow, now);

	ether_header->s_addr = config.device_macs[backend];
	ether_header->d_addr = config.backend_macs[backend];

	return backend + 1; // since 0 is the entry device
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
  lb_loop_iteration_begin(lb_get_buckets(balancer), lb_get_heap(balancer), lb_get_indices(balancer),
                          time);
}

void nf_add_loop_iteration_assumptions(unsigned lcore_id,
                                       time_t time) {
  lb_loop_iteration_assumptions(lb_get_buckets(balancer), lb_get_heap(balancer), lb_get_indices(balancer),
                                time);
}

void nf_loop_iteration_end(unsigned lcore_id,
                           time_t time) {
  lb_loop_iteration_end(lb_get_buckets(balancer), lb_get_heap(balancer), lb_get_indices(balancer),
                        time);
}
#endif

