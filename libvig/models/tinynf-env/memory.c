#include "env/memory.h"

#include <stdlib.h>

// TODO symbex linux-x86 env instead - need /dev/mem

bool tn_mem_allocate(uint64_t size, uintptr_t* out_addr)
{
	// don't forget about alignment!
	uintptr_t addr = (uintptr_t) calloc(1, 2 * size);
	*out_addr = addr + (size - (addr % size));
	return true;
}

void tn_mem_free(uintptr_t addr)
{
	free((void*) addr);
}

bool tn_mem_phys_to_virt(uintptr_t addr, uint64_t size, uintptr_t* out_virt_addr)
{
	*out_virt_addr = addr;
	return true;
}

bool tn_mem_virt_to_phys(uintptr_t addr, uintptr_t* out_phys_addr)
{
	*out_phys_addr = addr;
	return true;
}
