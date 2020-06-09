#pragma once

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

static inline void klee_make_symbolic(void *addr, size_t nbytes, const char *name) { abort(); }
static inline int klee_range(int begin, int end, const char *name) { abort(); }
static inline int klee_int(const char *name) { abort(); }
__attribute__((noreturn)) static inline void klee_silent_exit(int status) { exit(status); }
__attribute__((noreturn)) static inline void klee_abort(void) { abort(); }
static inline void klee_report_error(const char *file, int line, const char *message, const char *suffix) { abort(); }
static inline size_t klee_get_obj_size(void *ptr) { abort(); }
static inline uintptr_t klee_choose(uintptr_t n) { abort(); }
#define klee_assert assert
static inline unsigned klee_is_symbolic(uintptr_t n) { abort(); }
#define klee_note assert

static inline int klee_induce_invariants() { abort(); }
static inline void klee_forbid_access(void *ptr, int width, char *message) {}
static inline void klee_allow_access(void *ptr, int width) {}
static inline void klee_possibly_havoc(void *ptr, int width, char *name) {}
