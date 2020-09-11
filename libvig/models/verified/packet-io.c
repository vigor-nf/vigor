#include <stdlib.h>
#include <klee/klee.h>
#include "libvig/models/str-descr.h"
#include "libvig/verified/packet-io.h"
#include "packet-io-control.h"

#define MAX_CHUNK_SIZE 41
#define PREALLOC_CHUNKS 4

// struct Packet {
int global_sent;
/* int nic; */
/* int is_ipv4; */
int global_n_borrowed_chunks;
uint32_t global_packet_len;
uint32_t global_tot_len_borrowed;
uint8_t global_chunks[MAX_CHUNK_SIZE * PREALLOC_CHUNKS];
uint32_t global_chunk_lengths[PREALLOC_CHUNKS];
void *pkt_received = NULL;
bool receive_succeded = false;
struct ChunkLayout {
  bool set;
  uint32_t length;
  struct str_field_descr *fields;
  uint32_t n_fields;
  struct nested_field_descr *nests;
  uint32_t n_nests;
  const char *tname;
} global_chunk_layouts[PREALLOC_CHUNKS];

// void* global_packet_buffer;
//};

void set_packet_receive_success(bool received) { receive_succeded = received; }

void packet_set_next_chunk_layout(void *p, uint32_t length,
                                  struct str_field_descr *fields, int n_fields,
                                  struct nested_field_descr *nests, int n_nests,
                                  const char *tname) {
  klee_assert(global_n_borrowed_chunks < PREALLOC_CHUNKS);
  global_chunk_layouts[global_n_borrowed_chunks].length = length;
  global_chunk_layouts[global_n_borrowed_chunks].fields = fields;
  global_chunk_layouts[global_n_borrowed_chunks].n_fields = n_fields;
  global_chunk_layouts[global_n_borrowed_chunks].nests = nests;
  global_chunk_layouts[global_n_borrowed_chunks].n_nests = n_nests;
  global_chunk_layouts[global_n_borrowed_chunks].tname = tname;
  global_chunk_layouts[global_n_borrowed_chunks].set = true;
}

bool packet_is_last_borrowed_chunk(void *p, void *chunk) {
  return chunk ==
         &global_chunks[(global_n_borrowed_chunks - 1) * MAX_CHUNK_SIZE];
}

// The main IO primitive.
void packet_borrow_next_chunk(void *p, size_t length, void **chunk) {
  // TODO: add klee_access stuff
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)p, "p");
  klee_trace_param_u32(length, "length");
  klee_assert(receive_succeded);
  klee_assert(!global_sent);
  klee_assert(global_n_borrowed_chunks < PREALLOC_CHUNKS);
  klee_assert(length < MAX_CHUNK_SIZE);
  klee_assert(global_tot_len_borrowed + length <= global_packet_len);
  struct ChunkLayout *layout = &global_chunk_layouts[global_n_borrowed_chunks];
  klee_assert(layout->set);
  void *ret = &global_chunks[global_n_borrowed_chunks * MAX_CHUNK_SIZE];
  klee_trace_param_tagged_ptr(chunk, sizeof(void *), "chunk", layout->tname,
                              TD_OUT);
  klee_trace_extra_ptr(ret, layout->length, "the_chunk", layout->tname, TD_OUT);
  for (size_t i = 0; i < layout->n_fields; ++i) {
    klee_trace_extra_ptr_field(ret, layout->fields[i].offset,
                               layout->fields[i].width, layout->fields[i].name,
                               TD_OUT);
  }
  for (size_t i = 0; i < layout->n_nests; ++i) {
    if (layout->nests[i].count != 1) {
      klee_trace_extra_ptr_nested_field_arr(
          ret, layout->nests[i].base_offset, layout->nests[i].offset,
          layout->nests[i].width, layout->nests[i].count, layout->nests[i].name,
          TD_OUT);
    } else {
      klee_trace_extra_ptr_nested_field(
          ret, layout->nests[i].base_offset, layout->nests[i].offset,
          layout->nests[i].width, layout->nests[i].name, TD_OUT);
    }
  }
  global_chunk_lengths[global_n_borrowed_chunks] = length;
  global_n_borrowed_chunks++;
  global_tot_len_borrowed += length;
  *chunk = ret;
}

void packet_return_chunk(void *p, void *chunk) {
  klee_assert(0 < global_n_borrowed_chunks);
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)p, "p");
  uint32_t length = global_chunk_lengths[global_n_borrowed_chunks - 1];
  struct ChunkLayout *layout =
      &global_chunk_layouts[global_n_borrowed_chunks - 1];
  klee_assert(layout->set);
  klee_trace_param_tagged_ptr(chunk, layout->length, "the_chunk", layout->tname,
                              TD_IN);
  for (size_t i = 0; i < layout->n_fields; ++i) {
    klee_trace_param_ptr_field_directed(chunk, layout->fields[i].offset,
                                        layout->fields[i].width,
                                        layout->fields[i].name, TD_IN);
  }
  for (size_t i = 0; i < layout->n_nests; ++i) {
    if (layout->nests[i].count != 1) {
      klee_trace_param_ptr_nested_field_arr_directed(
          chunk, layout->nests[i].base_offset, layout->nests[i].offset,
          layout->nests[i].width, layout->nests[i].count, layout->nests[i].name,
          TD_IN);
    } else {
      klee_trace_param_ptr_nested_field_directed(
          chunk, layout->nests[i].base_offset, layout->nests[i].offset,
          layout->nests[i].width, layout->nests[i].name, TD_IN);
    }
  }
  klee_assert(!global_sent);
  global_n_borrowed_chunks--;
  klee_assert(global_chunks + MAX_CHUNK_SIZE * global_n_borrowed_chunks ==
              chunk);
}

void packet_state_total_length(void *p, uint32_t *len) {
  klee_trace_ret();
  klee_trace_param_just_ptr(p, sizeof(void *), "p");
  klee_trace_param_ptr_directed(len, sizeof(uint32_t), "len", TD_BOTH);
  klee_assert(p == pkt_received);
}

bool packet_receive(uint16_t src_device, void **p, uint32_t *len) {
  klee_trace_ret();
  klee_trace_param_u16(src_device, "src_devices");
  klee_trace_param_ptr_directed(p, sizeof(void *), "p", TD_OUT);
  klee_trace_param_ptr_directed(len, sizeof(uint32_t), "len", TD_BOTH);

  if (!receive_succeded) {
    return false;
  } else {
    pkt_received = *p;
    // TODO: klee_forbid access to the buffer
    //*p = &global_packet_buffer;
    klee_make_symbolic(global_chunks, sizeof(global_chunks), "packet_chunks");
    global_n_borrowed_chunks = 0;
    global_tot_len_borrowed = 0;
    global_sent = false;
    global_packet_len = *len; // klee_int("packet_len");
    for (uint32_t i = 0; i < PREALLOC_CHUNKS; ++i) {
      global_chunk_layouts[i].set = false;
    }
    return true;
  }
}

void packet_send(void *p, uint16_t dst_device) {
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)p, "p");
  klee_trace_param_u16(dst_device, "dst_device");
  klee_assert(!global_sent);
  global_sent = true;
}

void packet_free(void *p) {
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)p, "p");
  // klee_assert(!global_sent);
}

uint32_t packet_get_unread_length(void *p) {
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)p, "p");
  klee_assert(!global_sent);
  klee_assert(receive_succeded);
  klee_assert(global_tot_len_borrowed <= global_packet_len);
  return (uint32_t)(global_packet_len - global_tot_len_borrowed);
}
