#include <assert.h>
#include <sys/stat.h>

int __xstat(int ver, const char *path, struct stat *stat_buf) { assert(0); }
