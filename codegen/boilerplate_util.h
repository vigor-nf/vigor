#ifndef _BOILERPLATE_UTIL_H_INCLUDED_
#define _BOILERPLATE_UTIL_H_INCLUDED_

#include "include_ignored_by_verifast.h"

#ifdef _NO_VERIFAST_
#  define IGNORE(x) (void)(x)
#else //_NO_VERIFAST_
#  define IGNORE(x)
#endif //_NO_VERIFAST_

/*@
  fixpoint long long _wrap(long long x) { return x % INT_MAX; }
  @*/

// KLEE doesn't tolerate && in a klee_assume (see klee/klee#809),
// so we replace them with & during symbex but interpret them as && in the validator
#ifdef KLEE_VERIFICATION
#  define AND &
#else // KLEE_VERIFICATION
#  define AND &&
#endif // KLEE_VERIFICATION

static inline unsigned long long wrap(unsigned long long x)
//@ requires true;
//@ ensures result == _wrap(x) &*& INT_MIN <= result &*& result <= INT_MAX;
{
  //@ div_rem(x, INT_MAX);
  return x % INT_MAX;
}


#endif//_BOILERPLATE_UTIL_H_INCLUDED_
