#include <stdlib.h>
#include <klee/klee.h>
#include "lib/stubs/containers/str-descr.h"
#include "lib/packet-io.h"

#define MAX_CHUNK_SIZE 100
#define PREALLOC_CHUNKS 10

struct Packet {
  int sent;
  int nic;
  int is_ipv4;
  int n_borrowed_chunks;
  uint32_t packet_len;
  uint32_t tot_len_borrowed;
  uint8_t chunks[MAX_CHUNK_SIZE*PREALLOC_CHUNKS];
};

/* static struct Packet global_current_packet; */
/* static bool one_packet_already_received = false; */
/* static bool one_packet_already_sent = false; */

// The main IO primitive.
void packet_borrow_next_chunk(struct Packet* p, size_t length, uint8_t** chunk) {
  //TODO: add klee_access stuff
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)p, "p");
  klee_trace_param_u32(length, "length");
  klee_trace_param_ptr_directed(chunk, sizeof(uint8_t*), "chunk", TD_OUT);
  klee_assert(!p->sent);
  klee_assert(p->n_borrowed_chunks < PREALLOC_CHUNKS);
  klee_assert(length < MAX_CHUNK_SIZE);
  klee_assert(p->tot_len_borrowed + length <= p->packet_len);
  uint8_t* ret = &p->chunks[p->n_borrowed_chunks*MAX_CHUNK_SIZE];
  klee_trace_extra_ptr_arr(ret, sizeof(uint8_t), MAX_CHUNK_SIZE,
                           "the_chunk", "uint8_t", TD_OUT);
  p->n_borrowed_chunks++;
  p->tot_len_borrowed += length;
  *chunk = ret;
}

void packet_return_chunk(struct Packet* p, uint8_t* chunk) {
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)p, "p");
  klee_trace_param_arr_directed(chunk, sizeof(uint8_t), MAX_CHUNK_SIZE, "chunk", TD_IN);
  klee_assert(!p->sent);
  klee_assert(0 < p->n_borrowed_chunks);
  p->n_borrowed_chunks--;
  klee_assert(p->chunks + MAX_CHUNK_SIZE*p->n_borrowed_chunks == chunk);
}

bool packet_receive(uint16_t src_device, struct Packet** p) {
  klee_trace_ret();
  klee_trace_param_u16(src_device, "src_devices");
  klee_trace_param_ptr(p, sizeof(struct Packet*), "p");

  if (klee_int("received") == 0) {
    return false;
  } else {
    *p = malloc(sizeof(struct Packet));
    klee_make_symbolic(*p, sizeof(struct Packet), "packet");
    (**p).n_borrowed_chunks = 0;
    (**p).tot_len_borrowed = 0;
    (**p).nic = src_device;
    (**p).sent = false;
    klee_assume(sizeof(struct ether_hdr) <= (**p).packet_len);
    return true;
  }
}

void packet_send(struct Packet* p, uint16_t dst_device) {
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)p, "p");
  klee_trace_param_u16(dst_device, "dst_device");
  klee_assert(!p->sent);
  p->sent = true;
  free(p);
}

void packet_free(struct Packet* p) {
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)p, "p");
  klee_assert(!p->sent);
  free(p);
}

uint32_t packet_is_ipv4(struct Packet* p) {
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)p, "p");
  klee_assert(!p->sent);
  if (p->is_ipv4 == 0) {
    return false;
  } else {
    return true;
  }
}

uint16_t packet_get_port(struct Packet* p) {
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)p, "p");
  klee_assert(!p->sent);
  return p->nic;
}

// flooding is necessary for the bridge to function
// TODO why does this even exist?
void packet_flood(struct Packet* p,
                  uint16_t skip_device,
                  uint16_t nb_devices,
                  struct rte_mempool* clone_pool) {
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)p, "p");
  klee_trace_param_i32(skip_device, "skip_device");
  klee_trace_param_i32(nb_devices, "nb_devices");
  klee_trace_param_just_ptr(clone_pool, sizeof(struct rte_mempool*), "clone_pool");
  klee_assert(!p->sent);
  p->sent = true;
  free(p);
  //  klee_forbid_access(frame->buf_addr, sizeof(struct stub_mbuf_content),
  //                     "pkt flooded");
  //  klee_forbid_access(frame,
  //                     sizeof(struct rte_mbuf),
  //                     "pkt flooded");
}

uint32_t packet_get_unread_length(struct Packet* p)
{
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)p, "p");
  klee_assert(!p->sent);
  klee_assert(p->tot_len_borrowed <= p->packet_len);
  return (uint32_t)(p->packet_len - p->tot_len_borrowed);
}
