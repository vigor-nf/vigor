#ifndef _STATE_H_INCLUDED_
#define _STATE_H_INCLUDED_
#include "loop.h"
struct State {
  struct Map* dyn_map;
  struct Vector* dyn_keys;
  struct DoubleChain* dyn_heap;
  struct Vector* dyn_vals;
  uint32_t capacity;
  uint32_t dev_count;
};

struct State* alloc_state(uint32_t capacity, uint32_t dev_count);
#endif//_STATE_H_INCLUDED_
