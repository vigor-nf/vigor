#pragma once

#include <assert.h>
#include <stdint.h>

// TODO not sure those are actually needed
static inline void klee_intercept_reads(void *addr, const char *reader_name) {}
static inline void klee_intercept_writes(void *addr, const char *writer_name) {}

static inline void klee_make_symbolic(void *addr, size_t nbytes, const char *name) { assert(0); }
static inline int klee_range(int begin, int end, const char *name) { assert(0); }
static inline int klee_int(const char *name) { assert(0); }
__attribute__((noreturn)) static inline void klee_silent_exit(int status) { exit(status); }
__attribute__((noreturn)) static inline void klee_abort(void) { abort(); }
static inline void klee_report_error(const char *file, int line, const char *message, const char *suffix) { assert(0); }
static inline size_t klee_get_obj_size(void *ptr) { assert(0); }
static inline uintptr_t klee_choose(uintptr_t n) { assert(0); }
#define klee_assert assert
static inline unsigned klee_is_symbolic(uintptr_t n) { assert(0); }
#define klee_note klee_assert

// TODO not sure those are actuallyneeded
static inline void klee_alias_function(const char *fn_name, const char *new_fn_name) {}
static inline void klee_alias_function_regex(const char *fn_regex, const char *new_fn_name) {}
static inline void klee_alias_undo(const char *alias) {}

static inline int klee_induce_invariants() { assert(0); }
static inline void klee_forbid_access(void *ptr, int width, char *message) {}
static inline void klee_allow_access(void *ptr, int width) {}
static inline void klee_possibly_havoc(void *ptr, int width, char *name) {}
