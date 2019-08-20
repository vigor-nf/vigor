/*
 * Doesn't look like KLEE's malloc can be bypassed so may as well not waste
 * the memory
 */
#ifndef KLEE_VERIFICATION

#  include <assert.h>
#  include <stdalign.h>
#  include <stdbool.h>
#  include <stddef.h>
#  include <stdlib.h>
#  include <string.h>

#  define MALLOC_MEM_SIZE 80000000

extern void *malloc(size_t size);
extern void *realloc(void *ptr, size_t new_size);
extern void *calloc(size_t num, size_t size);
extern void free(void *ptr);

void *malloc(size_t size) {
  static char malloc_mem[MALLOC_MEM_SIZE]
      __attribute__((aligned(alignof(max_align_t))));
  static size_t malloc_index;

  if (malloc_index + size >= MALLOC_MEM_SIZE) {
    abort();
  }

  /* Ensure that memory blocks are aligned */
  if ((size % alignof(max_align_t)) != 0) {
    size += alignof(max_align_t) - (size % alignof(max_align_t));
  }

  void *ret = &malloc_mem[malloc_index];
  malloc_index += size;

  return ret;
}

void *realloc(void *ptr, size_t new_size) {
  if (ptr == NULL) {
    return malloc(new_size);
  }

  assert(false && "Not implemented yet");
}

void *calloc(size_t num, size_t size) {
  void *ret = malloc(num * size);
  memset(ret, 0, num * size);
  return ret;
}

void free(void *ptr) {}

#endif /* KLEE_VERIFICATION */
