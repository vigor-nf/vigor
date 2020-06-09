#include <strings.h>
#include <string.h>

// DPDK 17.11 uses this even though it's nonstandard
char* index(const char* s, int c)
{
	return strchr(s, c);
}
