/*===-- klee.h --------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===*/

#ifndef __KLEE_H__
#define __KLEE_H__

#include <assert.h>
#include <inttypes.h>
#include <stddef.h>
#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif
  // Types of the reader/writer for intercepts
  /* size is in bytes; value must be zero-extended if size < 8 */
  typedef uint64_t (*klee_reader)(uint64_t addr, unsigned offset, unsigned size);
  /* size is in bytes; value may be zero-padded if size < 8 */
  typedef void (*klee_writer)(uint64_t addr, unsigned offset, unsigned size, uint64_t value);

  /*
   * Intercepts reads to the specified block of memory,
   * redirecting them to the specified reader.
   * This can be used for fine-grained access control, or to execute code
   * on each read (such as when modeling hardware).
   */
  static inline void klee_intercept_reads(void* addr, const char* reader_name) {}

  /*
   * Intercepts writes to the specified block of memory,
   * redirecting them to the specified writer.
   * This can be used for fine-grained access control, or to execute code
   * on each write (such as when modeling hardware).
   */
  static inline void klee_intercept_writes(void* addr, const char* writer_name) {}
  /* Add an accesible memory object at a user specified location. It
   * is the users responsibility to make sure that these memory
   * objects do not overlap. These memory objects will also
   * (obviously) not correctly interact with external function
   * calls.
   */
  static inline void klee_define_fixed_object(void *addr, size_t nbytes) {}
  /* klee_make_symbolic - Make the contents of the object pointer to by \arg
   * addr symbolic.
   *
   * \arg addr - The start of the object.
   * \arg nbytes - The number of bytes to make symbolic; currently this *must*
   * be the entire contents of the object.
   * \arg name - A name used for identifying the object in messages, output
   * files, etc. If NULL, object is called "unnamed".
   */
  static inline void klee_make_symbolic(void *addr, size_t nbytes, const char *name) { assert(0); }
  /* klee_range - Construct a symbolic value in the signed interval
   * [begin,end).
   *
   * \arg name - A name used for identifying the object in messages, output
   * files, etc. If NULL, object is called "unnamed".
   */
  static inline int klee_range(int begin, int end, const char *name) { assert(0); }
  /*  klee_int - Construct an unconstrained symbolic integer.
   *
   * \arg name - An optional name, used for identifying the object in messages,
   * output files, etc.
   */
  static inline int klee_int(const char *name) { assert(0); }
  /* klee_silent_exit - Terminate the current KLEE process without generating a
   * test file.
   */
  __attribute__((noreturn))
  static inline void klee_silent_exit(int status) { exit(status); }
  /* klee_abort - Abort the current KLEE process. */
  __attribute__((noreturn))
  static inline void klee_abort(void) {
    abort();
  }

  /* klee_report_error - Report a user defined error and terminate the current
   * KLEE process.
   *
   * \arg file - The filename to report in the error message.
   * \arg line - The line number to report in the error message.
   * \arg message - A string to include in the error message.
   * \arg suffix - The suffix to use for error files.
   */
  __attribute__((noreturn))
  static inline void klee_report_error(const char *file,
			 int line,
			 const char *message,
			 const char *suffix) { assert(0); }
  /* called by checking code to get size of memory. */
  static inline size_t klee_get_obj_size(void *ptr) { assert(0); }
  /* print the tree associated w/ a given expression. */
  static inline void klee_print_expr(const char *msg, ...) {}
  /* NB: this *does not* fork n times and return [0,n) in children.
   * It makes n be symbolic and returns: caller must compare N times.
   */
  static inline uintptr_t klee_choose(uintptr_t n) { assert(0); }
  /* special klee assert macro. this assert should be used when path consistency
   * across platforms is desired (e.g., in tests).
   * NB: __assert_fail is a klee "special" function
   */
# define klee_assert assert

  /* Return true if the given value is symbolic (represented by an
   * expression) in the current state. This is primarily for debugging
   * and writing tests but can also be used to enable prints in replay
   * mode.
   */
  static inline unsigned klee_is_symbolic(uintptr_t n) { assert(0); }

  /* The following intrinsics are primarily intended for internal use
     and may have peculiar semantics. */

  static inline void klee_assume(uintptr_t condition);
# define klee_note(condition) ( \
                               klee_assert(condition),  \
                               klee_assume(condition)  \
                                )
  static inline void klee_warning(const char *message) {}
  static inline void klee_warning_once(const char *message) {}
  static inline void klee_prefer_cex(void *object, uintptr_t condition) {}
  static inline void klee_posix_prefer_cex(void *object, uintptr_t condition) {}
  static inline void klee_mark_global(void *object) {}

  /* Return a possible constant value for the input expression. This
     allows programs to forcibly concretize values on their own. */
#define KLEE_GET_VALUE_PROTO(suffix, type)	type klee_get_value##suffix(type expr)

  KLEE_GET_VALUE_PROTO(f, float);
  KLEE_GET_VALUE_PROTO(d, double);
  KLEE_GET_VALUE_PROTO(l, long);
  KLEE_GET_VALUE_PROTO(ll, long long);
  KLEE_GET_VALUE_PROTO(_i32, int32_t);
  KLEE_GET_VALUE_PROTO(_i64, int64_t);

#undef KLEE_GET_VALUE_PROTO

  /* Ensure that memory in the range [address, address+size) is
     accessible to the program. If some byte in the range is not
     accessible an error will be generated and the state
     terminated.

     The current implementation requires both address and size to be
     constants and that the range lie within a single object. */
  static inline void klee_check_memory_access(const void *address, size_t size) {}

  /* Enable/disable forking. */
  static inline void klee_set_forking(unsigned enable) {}

  /* klee_alias_function("foo", "bar") will replace, at runtime (on
     the current path and all paths spawned on the current path), all
     calls to foo() by calls to bar().  foo() and bar() have to exist
     and have identical types.  Use klee_alias_function("foo", "foo")
     to undo.  Be aware that some special functions, such as exit(),
     may not always work. */
  static inline void klee_alias_function(const char* fn_name, const char* new_fn_name) {}

  /* Similar to klee_alias_function, but uses a regex to match
     the function's name; e.g. klee_alias_function_regex("foo.*", "bar")
     will replace "foo", "foox", "foo123" with "bar".
     Particularly useful to replace a static function, which
     may be replicated many times with a suffixed name. */
  static inline void klee_alias_function_regex(const char* fn_regex, const char* new_fn_name) {}

  /* Undoes an alias (either a name or a regex). */
  static inline void klee_alias_undo(const char* alias) {}

  /* Print stack trace. */
  static inline void klee_stack_trace(void) {}

  /* Print range for given argument and tagged with name */
  static inline void klee_print_range(const char * name, int arg ) {}

  /* Open a merge */
  static inline void klee_open_merge() {}

  /* Merge all paths of the state that went through klee_open_merge */
  static inline void klee_close_merge() {}

  /* Get errno value of the current state */
  static inline int klee_get_errno(void) { assert(0); }

#define KLEE_TRACE_PARAM_PROTO(suffix, type) \
  static inline void klee_trace_param##suffix(type param, const char* name) {}
  KLEE_TRACE_PARAM_PROTO(f, float);
  KLEE_TRACE_PARAM_PROTO(d, double);
  KLEE_TRACE_PARAM_PROTO(l, long);
  KLEE_TRACE_PARAM_PROTO(ll, long long);
  KLEE_TRACE_PARAM_PROTO(_u16, uint16_t);
  KLEE_TRACE_PARAM_PROTO(_i32, int32_t);
  KLEE_TRACE_PARAM_PROTO(_u32, uint32_t);
  KLEE_TRACE_PARAM_PROTO(_i64, int64_t);
  KLEE_TRACE_PARAM_PROTO(_u64, uint64_t);
#undef KLEE_TRACE_PARAM_PROTO
  static inline void klee_trace_param_ptr(void* ptr, int width, const char* name) {}
  typedef enum TracingDirection {
    TD_NONE= 0,
    TD_IN = 1,
    TD_OUT = 2,
    TD_BOTH = 3
  } TracingDirection;
  static inline void klee_trace_param_ptr_directed(void* ptr, int width,
                                     const char* name,
                                     TracingDirection td) {}
  static inline void klee_trace_param_tagged_ptr(void* ptr, int width,
                                   const char* name, const char* type,
                                   TracingDirection td) {}
  static inline void klee_trace_param_just_ptr(void* ptr, int width, const char* name) {}
  static inline void klee_trace_param_fptr(void* ptr, const char* name) {}
  static inline void klee_trace_ret() {}
  static inline void klee_trace_ret_ptr(int width) {}
  static inline void klee_trace_ret_just_ptr(int width) {}

  static inline void klee_trace_param_ptr_field(void* ptr, int offset, int width, const char* name) {}
  static inline void klee_trace_param_ptr_field_directed(void* ptr, int offset,
                                           int width, const char* name,
                                           TracingDirection td) {}
  static inline void klee_trace_param_ptr_field_just_ptr(void* ptr, int offset,
                                           int width, const char* name) {}
  static inline void klee_trace_ret_ptr_field(int offset, int width, const char* name) {}
  static inline void klee_trace_ret_ptr_field_just_ptr(int offset, int width, const char* name) {}
  static inline void klee_trace_param_ptr_nested_field(void* ptr, int base_offset,
                                         int offset, int width, const char* name) {}
  static inline void klee_trace_param_ptr_nested_field_directed(void* ptr, int base_offset,
                                                  int offset, int width, const char* name,
                                                  TracingDirection td) {}
  static inline void klee_trace_ret_ptr_nested_field(int base_offset,
                                       int offset, int width, const char* name) {}
  static inline void klee_trace_extra_ptr(void* ptr, int width, const char* name, const char* type, TracingDirection td) {}
  static inline void klee_trace_extra_ptr_field(void* ptr, int offset, int width, const char* name, TracingDirection td) {}
  static inline void klee_trace_extra_ptr_field_just_ptr(void* ptr, int offset,
                                           int width, const char* name) {}
  static inline void klee_trace_extra_ptr_nested_field(void* ptr, int base_offset,
                                         int offset, int width, const char* name, TracingDirection td) {}
  static inline void klee_trace_extra_ptr_nested_nested_field(void* ptr, int base_base_offset,
                                                int base_offset, int offset,
                                                int width, const char* name, TracingDirection td) {}

  static inline void klee_forget_all() {}

  static inline int klee_induce_invariants() { assert(0); }

  static inline void klee_forbid_access(void* ptr, int width, char* message) {}
  static inline void klee_allow_access(void* ptr, int width) {}

  static inline void klee_dump_constraints() {}

  static inline void klee_possibly_havoc(void* ptr, int width, char* name) {}

#ifdef __cplusplus
}
#endif

#endif /* __KLEE_H__ */
