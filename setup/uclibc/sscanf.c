int __isoc99_sscanf(const char *str, const char *format, ...)
{
  va_list args;
  va_start(args, format);
  int ret = vsscanf(str, format, args);
  va_end(args);
  return ret;
}

