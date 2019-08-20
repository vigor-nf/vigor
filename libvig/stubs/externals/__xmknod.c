#include <assert.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

int __xmknod(int ver, const char *path, mode_t mode, dev_t *dev) { assert(0); }
