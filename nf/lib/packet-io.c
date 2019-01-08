#include <stdlib.h>
#include <assert.h>
#include <rte_ip.h>
#include <rte_mbuf.h>
#include "packet-io.h"

struct Packet {
   struct rte_mbuf* mbuf;
   char* unread_buf;
};

static struct Packet global_current_packet;

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

/*@
  fixpoint bool missing_chunks(list<pair<char*, int> > missing_chunks, char* start, char* end) {
    switch(missing_chunks) {
      case nil: return start == end;
      case cons(h,t): return switch(h) { case pair(beginning, span):
        return start <= beginning && beginning <= end &&
               end == beginning + span && missing_chunks(t, start, beginning);
      };
    }
  }

  predicate packetp(struct Packet* p, int nic, int type, list<char> unread, list<pair<char*, int> > missing_chunks) =
    p == &global_current_packet &*&
    p->mbuf |-> ?mbuf &*&
    p->unread_buf |-> ?unread_buf &*&
    mbuf_metap(mbuf, ?meta) &*&
    switch(meta) { case rte_mbuf_metac(port, ptype, doff, dlen, ba):
      return nic == port &*& type == ptype &*&
             ba <= unread_buf &*& unread_buf <= ba + dlen &*&
             ba + dlen <= (char*)UINTPTR_MAX &*&
             length(unread) == ba + dlen - unread_buf &*&
             true == missing_chunks(missing_chunks, ba, unread_buf);
    } &*&
    chars(unread_buf, length(unread), unread);
  @*/

// The main IO primitive.
char* packet_borrow_next_chunk(struct Packet* p, size_t length)
/*@ requires packetp(p, ?nic, ?type, ?unread, ?mc) &*&
             length <= length(unread); @*/
/*@ ensures packetp(p, nic, type, drop(length, unread), cons(pair(result, length), mc)) &*&
            chars(result, length, take(length, unread)); @*/
{
  //TODO: support mbuf chains.
  //@ open packetp(p, nic, type, unread, mc);
  char* ret = p->unread_buf;
  p->unread_buf += length;
  //@ assert length <= length(unread);
  return ret;
  //@ chars_split(ret, length);
  //@ close packetp(p, nic, type, drop(length, unread), cons(pair(ret, length), mc));
}

void packet_return_chunk(struct Packet* p, char* chunk)
/*@ requires packetp(p, ?nic, ?type, ?unread, cons(pair(chunk, ?len), ?mc)) &*&
             chars(chunk, len, ?chnk); @*/
/*@ ensures packetp(p, nic, type, append(chnk, unread), mc); @*/
{
  //@ open packetp(p, nic, type, unread, cons(pair(chunk, len), mc));
  p->unread_buf = chunk;
  //@ close packetp(p, nic, type, append(chnk, unread), mc);
}

uint16_t
rte_eth_rx_burst(uint16_t port_id, uint16_t queue_id,
                 struct rte_mbuf **rx_pkts, uint16_t nb_pkts);
/*@ requires *rx_pkts |-> _; @*/
/*@ ensures result == 0 ? *rx_pkts |-> _ :
              *rx_pkts |-> ?mb &*& mbufp(mb, ?buf) &*&
              switch(buf) { case rte_mbufc(port, ptype, doff, content):
                return port == port_id;
              }; @*/

uint16_t
rte_eth_tx_burst(uint16_t port_id, uint16_t queue_id,
                 struct rte_mbuf **tx_pkts, uint16_t nb_pkts);
/*@ requires *tx_pkts |-> ?mb &*& mbufp(mb, _) &*&
             nb_pkts == 1 &*& queue_id == 0; @*/
/*@ ensures result == 0 ? *tx_pkts |-> mb &*& mbufp(mb, _) : *tx_pkts |-> _ ; @*/

void
rte_pktmbuf_free(struct rte_mbuf* m);
/*@ requires mbufp(m, _); @*/
/*@ ensures true; @*/

struct rte_mbuf *rte_pktmbuf_clone(struct rte_mbuf *md, struct rte_mempool *mp);
/*@ requires mbufp(md, ?buf); @*/
/*@ ensures mbufp(md, buf) &*& (result == NULL) ? true : mbufp(result, buf); @*/

void rte_exit(int code, char* reason);
/*@ requires true; @*/
/*@ ensures false; @*/


/*@
  lemma void axiome_produce_glob_packet();
  requires true;
  ensures Packet_mbuf(&global_current_packet, _) &*&
          Packet_unread_buf(&global_current_packet, _);

  lemma void axiome_consume_glob_packet();
  requires Packet_mbuf(&global_current_packet, _) &*&
           Packet_unread_buf(&global_current_packet, _);
  ensures true;
  @*/

bool packet_receive(uint16_t src_device, struct Packet** p)
/*@ requires *p |-> _; @*/
/*@ ensures result ? *p |-> ?pp &*& packetp(pp, src_device, _, _, nil) : *p |-> _; @*/
{
  struct rte_mbuf* buf = NULL;
  uint16_t actual_rx_len = rte_eth_rx_burst(src_device, 0, &buf, 1);

  if (actual_rx_len != 0) {
    *p = &global_current_packet;
    //@ axiome_produce_glob_packet();
    //@ assert buf |-> ?b;
    //@ assert mbufp(b, ?mbuffer);
    (*p)->mbuf = buf;
    (*p)->unread_buf = (*p)->mbuf->buf_addr;
    /*@
      switch(mbuffer) { case rte_mbufc(port, ptype, doff, content):
       close packetp(*p, src_device, _, content, nil);
      }
      @*/
    return true;
  } else {
    return false;
  }
}

void packet_send(struct Packet* p, uint16_t dst_device)
/*@ requires packetp(p, _, _, _, nil); @*/
/*@ ensures true; @*/
{
  //@ open packetp(p, _, _, _, nil);
  //@ close mbufp(p->mbuf, _);
  uint16_t actual_tx_len = rte_eth_tx_burst(dst_device, 0, &p->mbuf, 1);
  if (actual_tx_len == 0) {
    rte_pktmbuf_free(p->mbuf);
  }
  //@ axiome_consume_glob_packet();
}

// Flood method for the bridge
void
packet_flood(struct Packet* p, uint16_t skip_device, uint16_t nb_devices,
             struct rte_mempool* clone_pool)
/*@ requires packetp(p, _, _, _, nil); @*/
/*@ ensures true; @*/
{
  //@ open packetp(p, _, _, _, nil);
  struct rte_mbuf* frame = p->mbuf;
  for (uint16_t device = 0; device < nb_devices; device++)
    /*@ invariant 0 <= device &*& device <= nb_devices &*&
                  mbufp(frame, _); @*/
  {
    if (device != skip_device) {
      struct rte_mbuf* copy = rte_pktmbuf_clone(frame, clone_pool);
      if (copy == NULL) {
        //@ assume(false);
        rte_exit(EXIT_FAILURE, "Cannot clone a frame for flooding");
      }
      uint16_t actual_tx_len = rte_eth_tx_burst(device, 0, &copy, 1);

      if (actual_tx_len == 0) {
        rte_pktmbuf_free(copy);
      }
    }
  }
  rte_pktmbuf_free(frame);
  //@ axiome_consume_glob_packet();
}

void packet_free(struct Packet* p)
/*@ requires packetp(p, _, _, _, nil); @*/
/*@ ensures true; @*/
{
  //@ open packetp(p, _, _, _, nil);
  rte_pktmbuf_free(p->mbuf);
  //@ axiome_consume_glob_packet();
}

bool packet_is_ipv4(struct Packet* p)
/*@ requires packetp(p, ?nic, ?type, ?unread, ?mc); @*/
/*@ ensures packetp(p, nic, type, unread, mc) &*&
            result == ((type & 0x10) == 0x10); @*/
{
  //@ open packetp(p, nic, type, unread, mc);
  return (p->mbuf->packet_type & 0x10) == 0x10;
  //return RTE_ETH_IS_IPV4_HDR(p->mbuf->packet_type);
  //@ close packetp(p, nic, type, unread, mc);
}

uint16_t packet_get_port(struct Packet* p)
/*@ requires packetp(p, ?nic, ?type, ?unread, ?mc); @*/
/*@ ensures packetp(p, nic, type, unread, mc) &*&
            result == nic; @*/
{
  //@ open packetp(p, nic, type, unread, mc);
  return p->mbuf->port;
  //@ close packetp(p, nic, type, unread, mc);
}
