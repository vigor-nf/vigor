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
  uint32_t chunk_lengths[PREALLOC_CHUNKS];
  struct ChunkLayout {
    bool set;
    uint32_t length;
    struct str_field_descr* fields;
    uint32_t n_fields;
    struct nested_field_descr* nests;
    uint32_t n_nests;
    const char* tname;
  } chunk_layouts[PREALLOC_CHUNKS];
};

void packet_set_next_chunk_layout(struct Packet* p, uint32_t length,
                                  struct str_field_descr* fields, int n_fields,
                                  struct nested_field_descr* nests, int n_nests,
                                  const char* tname) {
  klee_assert(p->n_borrowed_chunks < PREALLOC_CHUNKS);
  p->chunk_layouts[p->n_borrowed_chunks].length = length;
  p->chunk_layouts[p->n_borrowed_chunks].fields = fields;
  p->chunk_layouts[p->n_borrowed_chunks].n_fields = n_fields;
  p->chunk_layouts[p->n_borrowed_chunks].nests = nests;
  p->chunk_layouts[p->n_borrowed_chunks].n_nests = n_nests;
  p->chunk_layouts[p->n_borrowed_chunks].tname = tname;
  p->chunk_layouts[p->n_borrowed_chunks].set = true;
}

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
  struct ChunkLayout* layout = &p->chunk_layouts[p->n_borrowed_chunks];
  klee_assert(layout->set);
  uint8_t* ret = &p->chunks[p->n_borrowed_chunks*MAX_CHUNK_SIZE];
  klee_trace_extra_ptr(ret, layout->length, "the_chunk", layout->tname, TD_OUT);
  for (size_t i = 0; i < layout->n_fields; ++i) {
    klee_trace_extra_ptr_field(ret,
                               layout->fields[i].offset,
                               layout->fields[i].width,
                               layout->fields[i].name,
                               TD_OUT);
  }
  for (size_t i = 0; i < layout->n_nests; ++i) {
    klee_trace_extra_ptr_nested_field(ret,
                                      layout->nests[i].base_offset,
                                      layout->nests[i].offset,
                                      layout->nests[i].width,
                                      layout->nests[i].name,
                                      TD_OUT);
  }
  p->chunk_lengths[p->n_borrowed_chunks] = length;
  p->n_borrowed_chunks++;
  p->tot_len_borrowed += length;
  *chunk = ret;
}

void packet_return_chunk(struct Packet* p, uint8_t* chunk) {
  klee_assert(0 < p->n_borrowed_chunks);
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)p, "p");
  uint32_t length = p->chunk_lengths[p->n_borrowed_chunks - 1];
  struct ChunkLayout* layout = &p->chunk_layouts[p->n_borrowed_chunks - 1];
  klee_assert(layout->set);
  klee_trace_param_tagged_ptr(chunk, layout->length,
                              "the_chunk", layout->tname, TD_IN);
  for (size_t i = 0; i < layout->n_fields; ++i) {
    klee_trace_param_ptr_field_directed(chunk,
                                        layout->fields[i].offset,
                                        layout->fields[i].width,
                                        layout->fields[i].name,
                                        TD_IN);
  }
  for (size_t i = 0; i < layout->n_nests; ++i) {
    klee_trace_param_ptr_nested_field_directed(chunk,
                                               layout->nests[i].base_offset,
                                               layout->nests[i].offset,
                                               layout->nests[i].width,
                                               layout->nests[i].name,
                                               TD_IN);
  }
  klee_assert(!p->sent);
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
    for (uint32_t i = 0; i < PREALLOC_CHUNKS; ++i) {
      (**p).chunk_layouts[i].set = false;
    }
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
