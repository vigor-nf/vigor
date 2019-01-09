#ifndef _PROXY_DPDK_H_INCLUDED_
#define _PROXY_DPDK_H_INCLUDED_

#include <stdint.h>
#include <stdlib.h>
#include <rte_mbuf.h>

//TODO: profile this to make sure the extra funcall doesn't hurt perf.
// if it does

/*@
    inductive rte_mbufi = rte_mbufc(int, int, int, list<char>);
    inductive rte_mbuf_metai = rte_mbuf_metac(int, int, int, int, char*);
    predicate mbuf_metap(struct rte_mbuf *mbuf; rte_mbuf_metai val) =
      mbuf->buf_addr |-> ?ba &*&
      mbuf->buf_iova |-> ?bfa &*&
      mbuf->data_off |-> ?doff &*&
      mbuf->refcnt |-> ?rcnt &*&
      mbuf->nb_segs |-> ?nbsegs &*&
      mbuf->port |-> ?port &*&
      mbuf->ol_flags |-> ?olflags &*&
      mbuf->packet_type |-> ?ptype &*&
      mbuf->pkt_len |-> ?pktlen &*&
      mbuf->data_len |-> ?dlen &*&
      mbuf->vlan_tci |-> ?vlantci &*&
      mbuf->hash |-> ?hash &*&
      mbuf->vlan_tci_outer |-> ?vtcio &*&
      mbuf->buf_len |-> ?bl &*&
      mbuf->timestamp |-> ?tmstp &*&
      mbuf->udata64 |-> ?udata64 &*&
      mbuf->pool |-> ?pool &*&
      mbuf->next |-> ?next &*&
      mbuf->tx_offload |-> ?txoff &*&
      mbuf->priv_size |-> ?psize &*&
      mbuf->timesync |-> ?ts &*&
      mbuf->seqn |-> ?seqn &*&
      ba + dlen <= (char*)UINTPTR_MAX &*&
      val == rte_mbuf_metac(port, ptype, doff, dlen, (char*)ba) &*&
      doff == 0;
      //TODO: ^^^ is it really always so?

    predicate mbufp(struct rte_mbuf *mbuf; rte_mbufi val) =
      mbuf_metap(mbuf, ?meta) &*&
      switch(meta) { case rte_mbuf_metac(port, ptype, doff, dlen, ba):
        return chars(ba, dlen, ?content) &*&
        val == rte_mbufc(port, ptype, doff, content);
      };
@*/



uint16_t
proxy_rte_eth_rx_burst(uint16_t port_id, uint16_t queue_id,
                       struct rte_mbuf **rx_pkts, uint16_t nb_pkts);
/*@ requires *rx_pkts |-> _; @*/
/*@ ensures result == 0 ? *rx_pkts |-> _ :
              *rx_pkts |-> ?mb &*& mbufp(mb, ?buf) &*&
              switch(buf) { case rte_mbufc(port, ptype, doff, content):
                return port == port_id;
              }; @*/

uint16_t
proxy_rte_eth_tx_burst(uint16_t port_id, uint16_t queue_id,
                       struct rte_mbuf **tx_pkts, uint16_t nb_pkts);
/*@ requires *tx_pkts |-> ?mb &*& mbufp(mb, _) &*&
             nb_pkts == 1 &*& queue_id == 0; @*/
/*@ ensures result == 0 ? *tx_pkts |-> mb &*& mbufp(mb, _) : *tx_pkts |-> _ ; @*/

void
proxy_rte_pktmbuf_free(struct rte_mbuf* m);
/*@ requires mbufp(m, _); @*/
/*@ ensures true; @*/

struct rte_mbuf *proxy_rte_pktmbuf_clone(struct rte_mbuf *md, struct rte_mempool *mp);
/*@ requires mbufp(md, ?buf); @*/
/*@ ensures mbufp(md, buf) &*& (result == NULL) ? true : mbufp(result, buf); @*/

void proxy_rte_exit(int code, const char* reason);
/*@ requires true; @*/
/*@ ensures false; @*/

#endif//_PROXY_DPDK_H_INCLUDED_
