#ifndef _STATE_H_INCLUDED_
#define _STATE_H_INCLUDED_
#include "loop.h"
struct State {
  struct Map* flow_to_flow_id;
  struct Vector* flow_heap;
  struct DoubleChain* flow_chain;
  struct Vector* flow_id_to_backend_id;
  struct Map* ip_to_backend_id;
  struct Vector* backend_ips;
  struct Vector* backends;
  struct DoubleChain* active_backends;
  struct Vector* cht;
  uint32_t backend_capacity;
  uint32_t flow_capacity;
  uint32_t cht_height;
};

struct State* alloc_state(uint32_t backend_capacity, uint32_t flow_capacity, uint32_t cht_height);
#endif//_STATE_H_INCLUDED_
