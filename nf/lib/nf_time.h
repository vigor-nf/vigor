#ifndef NF_TIME_H_INCLUDED
#define NF_TIME_H_INCLUDED
#include <stdint.h>

// TODO use time_t from time.h - but this is used by VeriFast
// so even #ifdef-ing the time.h inclusion out doesn't work
#define vigor_time_t int64_t

#define VIGOR_TIME_SECONDS_MULTIPLIER (1000000000l)

//@ predicate last_time(vigor_time_t t);

/**
   A wrapper around the system time function. Returns the number of
   nanoseconds since the Epoch (1970-01-01 00:00:00 +0000 (UTC)).
   @returns the number of nanoseconds since Epoch.
*/
vigor_time_t current_time(void);
//@ requires last_time(?x);
//@ ensures result >= 0 &*& x <= result &*& last_time(result);

#endif//NF_TIME_H_INCLUDED
