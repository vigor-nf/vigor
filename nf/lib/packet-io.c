#include <stdlib.h>
#include <assert.h>
#include <rte_ip.h>
#include <rte_mbuf.h>

#include "packet-io.h"
#include "proxy-dpdk.h"

struct Packet {
   struct rte_mbuf* mbuf;
   uint8_t* unread_buf;
};

static struct Packet global_current_packet;

/*@
  fixpoint bool missing_chunks(list<pair<uint8_t*, int> > missing_chunks, uint8_t* start, uint8_t* end) {
    switch(missing_chunks) {
      case nil: return start == end;
      case cons(h,t): return switch(h) { case pair(beginning, span):
        return start <= beginning && beginning <= end &&
               end == beginning + span && missing_chunks(t, start, beginning);
      };
    }
  }

  predicate packetp(struct Packet* p, int nic, int type, list<uint8_t> unread, list<pair<uint8_t*, int> > missing_chunks) =
    p == &global_current_packet &*&
    p->mbuf |-> ?mbuf &*&
    p->unread_buf |-> ?unread_buf &*&
    mbuf_metap(mbuf, ?meta) &*&
    switch(meta) { case rte_mbuf_metac(port, ptype, doff, dlen, ba):
      return nic == port &*& type == ptype &*&
             ba <= unread_buf &*& unread_buf <= ba + dlen &*&
             (uint8_t*)ba + dlen <= (uint8_t*)UINTPTR_MAX &*&
             length(unread) == (char*)(void*)ba + dlen - (char*)(void*)unread_buf &*&
             true == missing_chunks(missing_chunks, ba, unread_buf);
    } &*&
    uchars(unread_buf, length(unread), unread);
  @*/

// The main IO primitive.
void packet_borrow_next_chunk(struct Packet* p, size_t length, void** chunk)
/*@ requires packetp(p, ?nic, ?type, ?unread, ?mc) &*&
             length <= length(unread) &*&
             *chunk |-> _; @*/
/*@ ensures *chunk |-> ?ptr &*&
            packetp(p, nic, type, drop(length, unread), cons(pair(ptr, length), mc)) &*&
            uchars(ptr, length, take(length, unread)); @*/
{
  //TODO: support mbuf chains.
  //@ open packetp(p, nic, type, unread, mc);
  *chunk = p->unread_buf;
  p->unread_buf += length;
  //@ assert length <= length(unread);
  //@ uchars_split(*chunk, length);
  //@ close packetp(p, nic, type, drop(length, unread), cons(pair(*chunk, length), mc));
}

void packet_return_chunk(struct Packet* p, void* chunk)
/*@ requires packetp(p, ?nic, ?type, ?unread, cons(pair(chunk, ?len), ?mc)) &*&
             uchars(chunk, len, ?chnk); @*/
/*@ ensures packetp(p, nic, type, append(chnk, unread), mc); @*/
{
  //@ open packetp(p, nic, type, unread, cons(pair(chunk, len), mc));
  p->unread_buf = chunk;
  //@ close packetp(p, nic, type, append(chnk, unread), mc);
}

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
/*@ ensures result ? *p |-> ?pp &*&
                     packetp(pp, src_device, _, ?unread, nil) &*&
                     sizeof(struct ether_hdr) <= length(unread)
                   : *p |-> _; @*/
{
  struct rte_mbuf* buf = NULL;
  uint16_t actual_rx_len = proxy_rte_eth_rx_burst(src_device, 0, &buf, 1);

  if (actual_rx_len != 0) {
    *p = &global_current_packet;
    //@ axiome_produce_glob_packet();
    //@ assert buf |-> ?b;
    //@ assert mbufp(b, ?mbuffer);
    (*p)->mbuf = buf;
    (*p)->unread_buf = (uint8_t*)(void*)(*p)->mbuf->buf_addr;
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
  uint16_t actual_tx_len = proxy_rte_eth_tx_burst(dst_device, 0, &p->mbuf, 1);
  if (actual_tx_len == 0) {
    proxy_rte_pktmbuf_free(p->mbuf);
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
      struct rte_mbuf* copy = proxy_rte_pktmbuf_clone(frame, clone_pool);
      if (copy == NULL) {
        //@ assume(false);
        proxy_rte_exit(EXIT_FAILURE, "Cannot clone a frame for flooding");
      }
      uint16_t actual_tx_len = proxy_rte_eth_tx_burst(device, 0, &copy, 1);

      if (actual_tx_len == 0) {
        proxy_rte_pktmbuf_free(copy);
      }
    }
  }
  proxy_rte_pktmbuf_free(frame);
  //@ axiome_consume_glob_packet();
}

void packet_free(struct Packet* p)
/*@ requires packetp(p, _, _, _, nil); @*/
/*@ ensures true; @*/
{
  //@ open packetp(p, _, _, _, nil);
  proxy_rte_pktmbuf_free(p->mbuf);
  //@ axiome_consume_glob_packet();
}

uint32_t packet_is_ipv4(struct Packet* p)
/*@ requires packetp(p, ?nic, ?type, ?unread, ?mc); @*/
/*@ ensures packetp(p, nic, type, unread, mc) &*&
            (result == 0 ?
              ((type & 0x10) != 0x10) :
              ((type & 0x10) == 0x10) &*& result == 1); @*/
{
  //@ open packetp(p, nic, type, unread, mc);
  return ((p->mbuf->packet_type & 0x10) == 0x10) ? 1u : 0;

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

uint32_t packet_get_unread_length(struct Packet* p)
/*@ requires packetp(p, ?nic, ?type, ?unread, ?mc); @*/
/*@ ensures packetp(p, nic, type, unread, mc) &*&
            result == length(unread); @*/
{
  //@ open packetp(p, nic, type, unread, mc);
  return (uint32_t)(((char*)p->mbuf->buf_addr + p->mbuf->data_len) - ((char*)(void*)p->unread_buf));
  //@ close packetp(p, nic, type, unread, mc);
}
