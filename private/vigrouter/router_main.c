#include "nf.h"
#include "config.h"

#include <rte_common.h>
#include <rte_ethdev.h>

#include "nf-log.h"
#include "nf-util.h"
#include "libvig/verified/boilerplate-util.h"

#include "state.h"

struct nf_config config;

struct State *state;

void nf_init(void) {
  state = alloc_state();
  if (state == NULL) {
    rte_exit(EXIT_FAILURE, "Not enough memory for state");
  }

  for (uint32_t n = 0; n < 128; n++) {
    lpm_update_elem(state->lpm, n << 24, 8, 1);
  }
  for (uint32_t n = 0; n < 128; n++) {
    lpm_update_elem(state->lpm, n, 32, 1);
  }
}

int nf_process(struct rte_mbuf *mbuf, vigor_time_t now) {

  struct ether_hdr *ether_header = nf_then_get_ether_header(mbuf_pkt(mbuf));
  uint8_t *ip_options;
  struct ipv4_hdr *ipv4_header =
      nf_then_get_ipv4_header(ether_header, mbuf_pkt(mbuf), &ip_options);
  if (ipv4_header == NULL) {
    NF_DEBUG("Not IPv4, dropping");
    return mbuf->port;
  }

  uint16_t dst_device = lpm_lookup_elem(state->lpm, ipv4_header->dst_addr);
  if (dst_device == mbuf->port)
    return mbuf->port;

  // Special method required during symbolic execution to avoid path explosion
  concretize_devices(&dst_device, rte_eth_dev_count());

  ether_header->s_addr = config.device_macs[dst_device];
  ether_header->d_addr = config.endpoint_macs[dst_device];

  return dst_device;
}
