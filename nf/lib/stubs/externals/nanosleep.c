#include <time.h>

int nanosleep(const struct timespec *req, struct timespec *rem)
{
	// Don't actually sleep
	return 0;
}
