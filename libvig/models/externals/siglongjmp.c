#include <setjmp.h>
#include <assert.h>

void siglongjmp(sigjmp_buf __env, int __val) { assert(0); }
