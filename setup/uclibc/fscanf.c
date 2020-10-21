int __isoc99_fscanf(FILE *stream, const char *format, ...)
{
  va_list args;
  va_start(args, format);
  int ret = vfscanf(stream, format, args);
  va_end(args);
  return ret;
}
