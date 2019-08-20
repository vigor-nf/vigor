// used with VeriFast, cannot use #pragma
#ifndef MBUF_CONTENT_H
#define MBUF_CONTENT_H

#include <rte_ether.h>
#include <rte_ip.h>
#include <rte_tcp.h>
#include "libvig/tcpudp.h"

// TODO: should autogenerate this file as well.
#include "ether_addr.h.gen.h"

// TODO more complete stub content?
// do change the total_len in rx if this is changed!
struct stub_mbuf_content {
  struct ether_hdr ether;
  struct ipv4_hdr ipv4;
  struct tcp_hdr tcp;
}
// We need to pack the structure so offsets are correct, but only if we're not
// within VeriFast, cause VeriFast doesn't know about it
#ifdef KLEE_VERIFICATION
__attribute__((packed))
#endif
;

// VeriFast definitions used in the tracing contracts
// The switch statement for ether_addrp is there to make VeriFast understand
// that the list has *exactly* 6 elements
/*@

    inductive ether_hdri = ether_hdrc(ether_addri, ether_addri, int);
    predicate ether_hdrp(struct ether_hdr *ether; ether_hdri hdr) =
      ether_addrp(&ether->d_addr, ?daddr) &*&
      ether_addrp(&ether->s_addr, ?saddr) &*&
      ether->ether_type |-> ?et &*&
      hdr == ether_hdrc(saddr, daddr, et);

    inductive ipv4_hdri = ipv4_hdrc(int, int, int, int, int, int, int, int, int, int);
    predicate ipv4_hdrp(struct ipv4_hdr* hdr; ipv4_hdri val) =
      hdr->version_ihl |-> ?vihl &*&
      hdr->type_of_service |-> ?tos &*&
      hdr->total_length |-> ?len &*&
      hdr->packet_id |-> ?pid &*&
      hdr->fragment_offset |-> ?foff &*&
      hdr->time_to_live |-> ?ttl &*&
      hdr->next_proto_id |-> ?npid &*&
      hdr->hdr_checksum |-> ?cksum &*&
      hdr->src_addr |-> ?saddr &*&
      hdr->dst_addr |-> ?daddr &*&
      val == ipv4_hdrc(vihl, tos, len, pid, foff, ttl, npid, cksum, saddr, daddr);

    inductive tcp_hdri = tcp_hdrc(int, int, int, int, int, int, int, int, int);
    predicate tcp_hdrp(struct tcp_hdr* hdr; tcp_hdri val) =
      hdr->src_port |-> ?srcp &*&
      hdr->dst_port |-> ?dstp &*&
      hdr->sent_seq |-> ?seq &*&
      hdr->recv_ack |-> ?ack &*&
      hdr->data_off |-> ?doff &*&
      hdr->tcp_flags |-> ?flags &*&
      hdr->rx_win |-> ?win &*&
      hdr->cksum |-> ?cksum &*&
      hdr->tcp_urp |-> ?urp &*&
      val == tcp_hdrc(srcp, dstp, seq, ack, doff, flags, win, cksum, urp);

    inductive tcpudp_hdri = tcpudp_hdrc(int, int);
    predicate tcpudp_hdrp(struct tcpudp_hdr* hdr; tcpudp_hdri val) =
      hdr->src_port |-> ?srcp &*&
      hdr->dst_port |-> ?dstp &*&
      val == tcpudp_hdrc(srcp, dstp);

    inductive user_bufi = user_bufc(ether_hdri, ipv4_hdri, tcp_hdri);
    predicate user_bufferp(struct stub_mbuf_content *buf; user_bufi ub) =
      ether_hdrp(&buf->ether, ?hdr) &*&
      ipv4_hdrp(&buf->ipv4, ?ipv4) &*&
      tcp_hdrp(&buf->tcp, ?tcp) &*&
      ub == user_bufc(hdr, ipv4, tcp);
      //FIXME: ^^ generalize for kinds of packets, not just ether+ipv4+tcp
@*/

#endif
