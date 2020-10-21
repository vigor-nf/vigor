#include "_externals.h"
#include "libvig/models/hardware.h"
#include "libvig/kernel/nfos_pci.h"

// GNU_SOURCE for fopencookie
#include <stdio.h>

#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include <klee/klee.h>

extern struct nfos_pci_nic *PCI_DEVICES;
extern int NUM_PCI_DEVICES;

// Because DPDK might call fflush on this file we need to be able to recognize
// it
static FILE *fopencookie_ret = NULL;

#ifdef NFOS
int vprintf1(const char *fmt, va_list va);
#endif

int fflush(FILE *stream) {
  klee_assert(stream == stderr || stream == stdout ||
              (stream != NULL && stream == fopencookie_ret));
  return 0;
}

int vfprintf(FILE *stream, const char *format, va_list __arg) {
  klee_assert(stream == stderr || stream == stdout ||
              (stream != NULL && stream == fopencookie_ret));
#if (defined NFOS) && (!defined KLEE_VERIFICATION)
  vprintf1(format, __arg);
#endif //(defined NFOS) && (!defined KLEE_VERIFICATION)

  return 0; // OK, whatever
}

FILE *fopencookie(void *cookie, const char *mode,
                  cookie_io_functions_t io_funcs) {
  fopencookie_ret = (FILE *)malloc(sizeof(FILE));
  ;
  klee_forbid_access(fopencookie_ret, sizeof(FILE), "fopencookie");
  return fopencookie_ret;
}

// We implement this here since it's common to multiple kinds of I/O: files and
// pipes
ssize_t write(int fd, const void *buf, size_t count) {
  // http://man7.org/linux/man-pages/man2/write.2.html

  // "According to POSIX.1, if count is greater than SSIZE_MAX, the result is
  // implementation-defined"
  klee_assert(count <= SSIZE_MAX);

  // "On Linux, write() (and similar system calls) will transfer at most
  // 0x7ffff000 (2,147,479,552) bytes,
  //  returning the number of bytes actually transferred."
  klee_assert(count <= 0x7ffff000);

  // "On success, the number of bytes written is returned (zero indicates
  // nothing was written).
  //  It is not an error if this number is smaller than the number of bytes
  //  requested."

  // Either we write to the stub pipe, or to an interrupt file
  if (fd == STUB_PIPE_FD_WRITE) {
    stub_pipe_write(buf, count);
    return count;
  }

  klee_assert(count == 4);

  for (int n = 0; n < NUM_PCI_DEVICES; n++) {
    if (fd == PCI_DEVICES[n].interrupts_fd) {
      if (*((uint32_t *)buf) == 0) {
        // Disabled - OK
      } else if (*((uint32_t *)buf) == 1) {
        // Enabled - OK
      } else {
        klee_abort();
      }
      return count;
    }
  }

  klee_abort();
}
