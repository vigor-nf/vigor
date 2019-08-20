#include <assert.h>
#include <stdlib.h>

long long __strtoll_internal(const char *__nptr, char **__endptr, int __base,
                             int __group) {
  // __group shall be 0 or the behavior of __strtoll_internal() is undefined
  assert(__group == 0);

  // __strtoll_internal(__nptr, __endptr, __base, 0) has the same specification
  // as strtoll(__nptr, __endptr, __base)
  return strtoll(__nptr, __endptr, __base);
}
