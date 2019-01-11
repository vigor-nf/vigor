#include <assert.h>
#include <fcntl.h>

int __libc_open(const char *pathname, int flags, mode_t mode)
{
	return open(pathname, flags, mode);
}
