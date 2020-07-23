#include <sched.h>
#include <pthread.h>

#ifdef KLEE_VERIFICATION
#  include <klee/klee.h>
#endif

pthread_t pthread_self(void) {
  // We are on CPU 0 - always
  return 0;
}

int pthread_getaffinity_np(pthread_t thread, size_t cpusetsize,
                           cpu_set_t *cpuset) {
#ifdef KLEE_VERIFICATION
  // We're running in a symbolic executor. the concept of "affinity" is
  // meaningless
  int ret = klee_int("pthread_getaffinity_np_return");
  klee_assume(ret >= 0);
#else
  // We're not verifying here, pretend that the function succeeded
  int ret = 0;
#endif

  // However, we might be given uninitialized memory, so we need to set it
  if (ret >= 0) {
    // TODO all bits should be symbols...
    CPU_ZERO(cpuset);
    CPU_SET(0, cpuset);
  }

  return ret;
}

int pthread_setaffinity_np(pthread_t thread, size_t cpusetsize,
                           const cpu_set_t *cpuset) {
  // Same remark as getaffinity
#ifdef KLEE_VERIFICATION
  int ret = klee_int("pthread_getaffinity_np_return");
  klee_assume(ret >= 0);
#else
  int ret = 0;
#endif
  return ret;
}

int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
                   void *(*start_routine)(void *), void *arg) {
  // "On success, pthread_create() returns 0; on error, it returns an error
  // number, and the contents of *thread are undefined."
  // -- http://man7.org/linux/man-pages/man3/pthread_create.3.html
  return 0;
}

int pthread_setname_np(pthread_t thread, const char *name) {
  // just ignore it - we don't support getname anyway

  // "On success, these functions return 0; on error, they return a nonzero
  // error number."
  // -- http://man7.org/linux/man-pages/man3/pthread_setname_np.3.html
  return 0;
}

int  pthread_barrier_init(pthread_barrier_t *barrier,
       const pthread_barrierattr_t *attr, unsigned count) {
  // "Upon successful completion, these functions shall return zero; otherwise, an error
  // number shall be returned to indicate the error."
  // -- https://linux.die.net/man/3/pthread_barrier_init
  return 0;
}

int pthread_barrier_wait(pthread_barrier_t *barrier) {
  // "Upon successful completion, the pthread_barrier_wait() function shall return
  // PTHREAD_BARRIER_SERIAL_THREAD for a single (arbitrary) thread synchronized at the
  // barrier and zero for each of the other threads."
  // -- https://linux.die.net/man/3/pthread_barrier_wait
  return 0;
}

int pthread_cancel(pthread_t thread) {
  // "On success, pthread_cancel() returns 0;"
  // -- https://linux.die.net/man/3/pthread_cancel
  return 0;
}

int pthread_join(pthread_t thread, void **retval) {
  // "On success, pthread_join() returns 0;"
  // -- https://linux.die.net/man/3/pthread_join
  return 0;
}

