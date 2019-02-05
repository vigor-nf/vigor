#ifndef _POLICER_DATA_H_INCLUDED_
#define _POLICER_DATA_H_INCLUDED_

#include "stdbool.h"

#include "ip_addr.h.gen.h"
#include "dynamic_value.h.gen.h"

#include "lib/stubs/core_stub.h"

struct Map;
struct Vector;
struct DoubleChain;

struct DynamicFilterTable {
  struct Map* map;
  struct DoubleChain* heap;
  struct Vector* keys;
  struct Vector* values;
};

#endif//_POLICER_DATA_H_INCLUDED_
