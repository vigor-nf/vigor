#ifndef _DYNAMIC_VALUE_H_INCLUDED_
#define _DYNAMIC_VALUE_H_INCLUDED_

#include "stdint.h"
#include "lib/nf_time.h"

struct DynamicValue {
  uint32_t bucket_size;
  vigor_time_t bucket_time;
};

#endif//_DYNAMIC_VALUE_H_INCLUDED_
