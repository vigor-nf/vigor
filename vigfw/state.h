#ifndef _STATE_H_INCLUDED_
#define _STATE_H_INCLUDED_
#include "loop.h"
struct State {
  struct Map* fm;
  struct Vector* fv;
  struct Vector* int_devices;
  struct DoubleChain* heap;
  int max_flows;
  uint32_t fw_device;
};

struct State* alloc_state(int max_flows, uint32_t fw_device);
#endif//_STATE_H_INCLUDED_
