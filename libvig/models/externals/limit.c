#include <sys/time.h>
#include <sys/resource.h>
#include <assert.h>

#ifdef KLEE_VERIFICATION
  #include <klee/klee.h>
#endif

//"The getrlimit() and setrlimit() system calls get and set resource limits."
// -- https://man7.org/linux/man-pages/man2/getrlimit.2.html

#ifdef KLEE_VERIFICATION
static int rlim_max = 0;
#endif

int getrlimit(__rlimit_resource_t resource, struct rlimit *rlim) {
  //We need to only support only this resource for now
  assert(resource == RLIMIT_NOFILE);
#ifdef KLEE_VERIFICATION
  rlim->rlim_cur = klee_int("getrlimit_rlim_cur_ret");
  rlim_max = klee_int("rlim_max");
  rlim->rlim_max = rlim_max;
#endif
  return 0;
}

int setrlimit(__rlimit_resource_t resource, const struct rlimit *rlim) {
  //We need to only support only this resource for now
  assert(resource == RLIMIT_NOFILE);
  //Do not let increase beyond maximum
#ifdef KLEE_VERIFICATION
  klee_assert(rlim->rlim_cur <= rlim_max);
#endif
  return 0;
}
