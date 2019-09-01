#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

/*
 * This checks for buffer overflows but we're memory safe so we don't
 * need the check. Otherwise it's the same as snprintf.
 */
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
