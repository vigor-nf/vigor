#ifndef _PACKET_HEADERS_H_INCLUDED_
#define _PACKET_HEADERS_H_INCLUDED_

#include "stubs/mbuf_content.h"

/*@
  inductive phdr = ether_hdr(ether_hdri)
                 | ip_hdr(ipv4_hdri)
                 | tcp_hdr(tcp_hdri);

  lemma list<phdr> add_ether_header(list<phdr> prev, void* chunk);
  requires ether_hdrp(chunk, ?eh);
  ensures ether_hdrp(chunk, eh) &*& result == cons(ether_hdr(eh), prev);

  lemma list<phdr> add_ipv4_header(list<phdr> prev, void* chunk);
  requires ipv4_hdrp(chunk, ?ih);
  ensures ipv4_hdrp(chunk, ih) &*& result == cons(ip_hdr(ih), prev);

  lemma list<phdr> add_tcp_header(list<phdr> prev, void* chunk);
  requires tcp_hdrp(chunk, ?th);
  ensures tcp_hdrp(chunk, th) &*& result == cons(tcp_hdr(th), prev);
  @*/

#endif//_PACKET_HEADERS_H_INCLUDED_
