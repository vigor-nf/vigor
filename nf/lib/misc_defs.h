#ifndef _MISC_DEF_H
#define _MISC_DEF_H

#define PATH_MAX 4096

#ifndef KLEE_VERIFICATION

#define hidden __attribute__((__visibility__("hidden")))
#define weak_alias(old, new) \
	extern __typeof(old) new __attribute__((__weak__, __alias__(#old)))

#undef __BEGIN_DECLS
#undef __END_DECLS

#ifdef __cplusplus
# define __BEGIN_DECLS extern "C" {
# define __END_DECLS }

#else /* __cplusplus */

# define __BEGIN_DECLS /* empty */
# define __END_DECLS /* empty */

#endif /* __cplusplus */

#define __nonnull(x) __attribute__((nonnull x))
#define __THROW

#define SSIZE_MAX INT_MAX

#endif /* KLEE_VERIFICATION */



#endif
