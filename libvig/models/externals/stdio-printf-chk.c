#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

// Family of printf functions that include buffer overflow checks.
// But in KLEE we don't need the checks here (KLEE does it), and in NFOS we run verified code,
// so we don't need the checks.

int __fprintf_chk(FILE *stream, int flag, const char *format, ...) {
  va_list args;
  va_start(args, format);
  int ret = vfprintf(stream, format, args);
  va_end(args);

  return ret;
}

int __printf_chk(int flag, const char *format, ...) {
  va_list args;
  va_start(args, format);
  int ret = vprintf(format, args);
  va_end(args);

  return ret;
}

int __snprintf_chk(char *str, size_t maxlen, int flag, size_t strlen,
                   const char *format, ...) {
  /* If strlen is less than maxlen, the function shall abort and the program
   * shall exit */
  if (strlen < maxlen) {
    abort();
  }

  va_list args;
  va_start(args, format);
  int ret = vsnprintf(str, maxlen, format, args);
  va_end(args);

  return ret;
}
