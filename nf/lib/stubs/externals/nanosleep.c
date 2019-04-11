#include <time.h>

int nanosleep(const struct timespec *req, struct timespec *rem)
{
	/* Don't actually sleep. TODO: Check if this is fine */
	return 0;
}
