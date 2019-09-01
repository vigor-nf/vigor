#include <stdio.h>
#include <stdarg.h>

/*
 * This checks for buffer overflows but we're memory safe so we don't
 * need the check. Otherwise it's the same as printf.
 */
int __printf_chk(int flag, const char *format, ...) {
  va_list args;
  va_start(args, format);
  int ret = vprintf(format, args);
  va_end(args);

  return ret;
}
