#include <numa.h>
#include <numaif.h>
#include <stdbool.h>

#include <klee/klee.h>

static int NUMA_AVAILABLE = 42;
static bool NUMA_NODEMASK_CREATED = false;

int numa_available(void) {
  // Before any other calls in this library can be used numa_available() must be
  // called. If it returns -1, all other functions in this library are
  // undefined.
  if (NUMA_AVAILABLE == 42) {
    NUMA_AVAILABLE = -1;
    // let's not double paths, just expose the dpdk bug...
    // NUMA_AVAILABLE = klee_range(-1, 1, "numa_available"); // 1 is exclusive,
    // this this will be -1 or 0 true;
  }
  return NUMA_AVAILABLE;
}

struct bitmask *numa_allocate_nodemask() {
  klee_assert(NUMA_AVAILABLE == 0);

  klee_assert(!NUMA_NODEMASK_CREATED);
  NUMA_NODEMASK_CREATED = true;

  struct bitmask *mask = (struct bitmask *)malloc(sizeof(struct bitmask));
  // The bitmask is zero-filled.
  // -- https://linux.die.net/man/3/numa_alloc_onnode
  memset(mask, 0, sizeof(struct bitmask));
  return mask;
}

void numa_bitmask_free(struct bitmask *bmp) {
  klee_assert(NUMA_AVAILABLE == 0);

  // It is an error to attempt to free this bitmask twice.
  // --https://linux.die.net/man/3/numa_alloc_onnode
  klee_assert(NUMA_NODEMASK_CREATED);
  NUMA_NODEMASK_CREATED = false;

  free(bmp);
}

long get_mempolicy(int *policy, const unsigned long *nmask,
                   unsigned long maxnode, void *addr, int flags) {
  // http://man7.org/linux/man-pages/man2/get_mempolicy.2.html
  if (flags == 0) {
    // When flags is 0, addr must be specified as NULL.
    klee_assert(addr == NULL);

    // If flags is specified as 0, then information about the calling
    // thread's default policy (as set by set_mempolicy(2)) is returned, in
    // the buffers pointed to by mode and nodemask.  The value returned in
    // these arguments may be used to restore the thread's policy to its
    // state at the time of the call to get_mempolicy() using set_mempolicy(2).
    *policy = 0;

    // On success, get_mempolicy() returns 0; on error, -1 is returned and
    // errno is set to indicate the error.
    return 0;
  }

  klee_abort();
}
