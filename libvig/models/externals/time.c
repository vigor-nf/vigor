#include <time.h>

#include "../hardware.h"

int nanosleep(const struct timespec *req, struct timespec *rem){
   // https://man7.org/linux/man-pages/man2/nanosleep.2.html
   // On successfully sleeping for the requested interval, nanosleep()
   // returns 0.
   time_t sec = req->tv_sec;
   long nsec = req->tv_nsec;
   TIME += sec*1E9 + nsec;
   return 0;
}
