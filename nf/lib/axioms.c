
#include <stdint.h>
#include <stdlib.h>
#include <rte_mbuf.h>
#include "lib/proxy-dpdk.h"

uint16_t
proxy_rte_eth_rx_burst(uint16_t port_id, uint16_t queue_id,
                       struct rte_mbuf **rx_pkts, uint16_t nb_pkts)
/*@ requires *rx_pkts |-> _; @*/
/*@ ensures result == 0 ? *rx_pkts |-> _ :
              *rx_pkts |-> ?mb &*& mbufp(mb, ?buf) &*&
              switch(buf) { case rte_mbufc(port, ptype, doff, content):
                return port == port_id &*&
                       sizeof(struct ether_hdr) <= length(content);
              }; @*/
{
  //@ assume(false);
  return 0;
}

uint16_t
proxy_rte_eth_tx_burst(uint16_t port_id, uint16_t queue_id,
                       struct rte_mbuf **tx_pkts, uint16_t nb_pkts)
/*@ requires *tx_pkts |-> ?mb &*& mbufp(mb, _) &*&
             nb_pkts == 1 &*& queue_id == 0; @*/
/*@ ensures result == 0 ? *tx_pkts |-> mb &*& mbufp(mb, _) : *tx_pkts |-> _ ; @*/
{
  //@ assume(false);
  return 0;
}

void proxy_rte_pktmbuf_free(struct rte_mbuf* m)
/*@ requires mbufp(m, _); @*/
/*@ ensures true; @*/
{
  //@ assume(false);
}

struct rte_mbuf *proxy_rte_pktmbuf_clone(struct rte_mbuf *md, struct rte_mempool *mp)
/*@ requires mbufp(md, ?buf); @*/
/*@ ensures mbufp(md, buf) &*& (result == NULL) ? true : mbufp(result, buf); @*/
{
  //@ assume(false);
}

void proxy_rte_exit(int code, const char* reason)
/*@ requires true; @*/
/*@ ensures false; @*/
{
  //@ assume(false);
}
