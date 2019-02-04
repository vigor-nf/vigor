#ifndef _DYNAMIC_VALUE_H_INCLUDED_
#define _DYNAMIC_VALUE_H_INCLUDED_

#include "stdint.h"

struct DynamicValue {
  uint32_t bucket_size;
  uint64_t bucket_time;
};

#endif//_DYNAMIC_VALUE_H_INCLUDED_
