#include "dsos_msr.h"

uint64_t dsos_rdmsr(uint32_t id)
{
	uint64_t ret;
	asm volatile ( "rdmsr" : "=A" (ret) : "c" (id) );
	return ret;
}
