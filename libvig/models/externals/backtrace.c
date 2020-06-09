#include <execinfo.h>
#include <stddef.h>

// Not great but we can't emulate an arbitrarily-sized backtrace,
// and anyway this is in a panic handler so not a huge deal since
// it can only happen at initialization time, not while processing packets

int backtrace(void **buffer, int size)
{
  return 0;
}

char **backtrace_symbols(void *const *buffer, int size)
{
  return NULL;
}
