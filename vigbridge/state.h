#ifndef _STATE_H_INCLUDED_
#define _STATE_H_INCLUDED_
#include "loop.h"
struct State {
  struct Map* dyn_map;
  struct Vector* dyn_keys;
  struct Vector* dyn_vals;
  struct Map* st_map;
  struct Vector* st_vec;
  struct DoubleChain* dyn_heap;
  uint32_t capacity;
  uint32_t stat_capacity;
  uint32_t dev_count;
};

struct State* alloc_state(uint32_t capacity, uint32_t stat_capacity, uint32_t dev_count);
#endif//_STATE_H_INCLUDED_
