#include "env/memory.h"

#include <stdlib.h>

// TODO symbex linux-x86 env instead - need /dev/mem

bool tn_mem_allocate(size_t size, void** out_addr)
{
	// don't forget about alignment!
	uintptr_t addr = (uintptr_t) calloc(1, 2 * size);
	*out_addr = (void*) (addr + (size - (addr % size)));
	return true;
}

void tn_mem_free(void* addr)
{
	// Do not free due to the alignment issues above, anyway this is only called in cases of failure
}

bool tn_mem_phys_to_virt(uintptr_t addr, size_t size, void** out_virt_addr)
{
	*out_virt_addr = (void*) addr;
	return true;
}

bool tn_mem_virt_to_phys(void* addr, uintptr_t* out_phys_addr)
{
	*out_phys_addr = (uintptr_t) addr;
	return true;
}
