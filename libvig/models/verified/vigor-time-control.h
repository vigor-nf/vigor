#ifndef _MY_TIME_STUB_CONTROL_H_INCLUDED_
#define _MY_TIME_STUB_CONTROL_H_INCLUDED_

#include <stdint.h>
#include "libvig/verified/vigor-time.h"

vigor_time_t start_time(void);
//@ requires true;
//@ ensures result >= 0 &*& last_time(result);

vigor_time_t restart_time(void);

vigor_time_t get_start_time(void);

#endif //_MY_TIME_STUB_CONTROL_H_INCLUDED_
