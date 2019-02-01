#ifndef _BRIDGE_DATA_H_INCLUDED_
#define _BRIDGE_DATA_H_INCLUDED_

#include "stdbool.h"
#include "lib/stubs/core_stub.h"

#include "stat_key.h.gen.h"
#include "dyn_value.h.gen.h"

struct Map;
struct Vector;
struct DoubleChain;


struct DynamicFilterTable {
  struct Map* map;
  struct DoubleChain* heap;
  struct Vector* keys;
  struct Vector* values;
};

struct StaticFilterTable {
  struct Map* map;
  struct Vector* keys;
};

#endif//_BRIDGE_DATA_H_INCLUDED_
