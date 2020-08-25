#include "env/time.h"

#include "libvig/models/hardware.h"

void tn_sleep_us(uint64_t microseconds) { TIME += microseconds * 1000; }
