#include <limits.h>
#include <sched.h>
#include <assert.h>

// No man entry for this function. But it counts CPUs with certain masks.
// In our case, we can only have 1 CPU, so let's return that.
int
__sched_cpucount (size_t setsize, const cpu_set_t *setp) {
  assert(setp != NULL);
  return 1;
}
