#include <stdlib.h>
#include <assert.h>
#include <rte_ip.h>
#include <rte_mbuf.h>

#include "packet-io.h"

int8_t* global_unread_buf;
size_t global_total_length;
size_t global_read_length;

/*@
  fixpoint bool missing_chunks(list<pair<int8_t*, int> > missing_chunks, int8_t* start, int8_t* end) {
    switch(missing_chunks) {
      case nil: return start == end;
      case cons(h,t): return switch(h) { case pair(beginning, span):
        return start <= beginning && beginning <= end &&
               end == beginning + span && missing_chunks(t, start, beginning);
      };
    }
  }

  fixpoint int borrowed_len(list<pair<int8_t*, int> > missing_chunks) {
    switch(missing_chunks) {
      case nil: return 0;
      case cons(h,t): return switch(h) { case pair(beginning, span):
        return span + borrowed_len(t);
      };
    }
  }

  predicate packetp(void* p, list<int8_t> unread, list<pair<int8_t*, int> > missing_chunks) =
    global_unread_buf |-> ?unread_buf &*&
    switch(meta) { case rte_mbuf_metac(port, ptype, doff, dlen, ba):
      return p <= unread_buf &*& unread_buf <= p + borrowed_len(missing_chunks) + length(unread) &*&
             (int8_t*)p + borrowed_len(missing_chunks) + length(unread) <= (int8_t*)UINTPTR_MAX &*&
             borrowed_len(missing_chunks) + (int8_t*)p == (char*)(void*)unread_buf &*&
             true == missing_chunks(missing_chunks, ba, unread_buf);
    } &*&
    chars(unread_buf, length(unread), unread);
  @*/

// The main IO primitive.
void packet_borrow_next_chunk(void* p, size_t length, void** chunk)
{
  //TODO: support mbuf chains.
  *chunk = global_unread_buf;
  global_unread_buf += length;
  global_read_length += length;
}

void packet_return_chunk(void* p, void* chunk)
{
  global_unread_buf = (int8_t*)chunk;
}

bool packet_receive(uint16_t src_device, void** p, uint16_t* len)
{
  global_total_length = *len;
  global_read_length = 0;
  global_unread_buf = (int8_t*)*p;
}

void packet_send(void* p, uint16_t dst_device)
{
  global_unread_buf = NULL;
}

// Flood method for the bridge
void
packet_flood(void* p, uint16_t skip_device, uint16_t nb_devices)
{
  global_unread_buf = NULL;
}

void packet_free(void* p)
{
  global_unread_buf = NULL;
}

uint32_t packet_get_unread_length(void* p)
{
  return global_total_length - global_read_length;
}
