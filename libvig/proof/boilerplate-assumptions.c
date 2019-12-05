#include "../verified/boilerplate-util.h"

// The following functions are by no means implementations of a CRC32 hash
// algorithm, but rather are stubs marking our assumption about correctness of
// the implementation of a builtin hash functions that map into x86
// instructions.
unsigned __builtin_ia32_crc32si(unsigned acc, unsigned int x)
/*@ requires true; @*/
/*@ ensures result == crc32_hash(acc, x); @*/
{
  //@ assume(false);
  return x;
}
unsigned long long __builtin_ia32_crc32di(unsigned long long acc,
                                          unsigned long long x)
/*@ requires true; @*/
/*@ ensures result == crc32_hash(acc, x); @*/
{
  //@ assume(false);
  return x;
}
