#include <unistd.h>
#include "_externals.h"

#include <stdbool.h>
#include <signal.h>

#include <sys/syscall.h>
#include <sys/types.h>

#include <klee/klee.h>


unsigned int sleep(unsigned int seconds) {
  // Whatever, code shouldn't use sleep anyway
  // If this exposes bugs, great!
  return 0;
}

uid_t getuid(void) {
  // No errors: "These functions are always successful."
  // -- http://man7.org/linux/man-pages/man2/getuid.2.html
  return 0; // We are root! well, we pretend to be, at least
}

long syscall(long number, ...) {
  // 0 is a kernel thing, 1 is init, so let's say 2
  if (number == SYS_gettid) {
    return 2;
  }

  // Not supported!
  klee_abort();
}

int getpagesize(void) { return PAGE_SIZE; }

int __syscall_rt_sigaction(int signum, const struct sigaction *act,
                           struct sigaction *oldact, size_t _something) {
  // We don't support signals, so no need to do anything

  // "sigaction() returns 0 on success; on error, -1 is returned, and errno is
  // set to indicate the error."
  // -- http://man7.org/linux/man-pages/man2/sigaction.2.html
  return 0;
}

int sigaction(int signum, const struct sigaction *act,
              struct sigaction *oldact) {
  // Same as above
  return 0;
}


static bool pipe_created = false;

int pipe(int pipefd[2]) {
  // http://man7.org/linux/man-pages/man2/pipe.2.html

  klee_assert(!pipe_created);
  pipe_created = true;

  // "The array pipefd is used to return two file descriptors referring to the
  //  ends of the pipe.
  //  pipefd[0] refers to the read end of the pipe.
  //  pipefd[1] refers to the write end of the pipe."
  pipefd[0] = STUB_PIPE_FD_READ;
  pipefd[1] = STUB_PIPE_FD_WRITE;

  // "On success, zero is returned.  On error, -1 is returned, and errno is set
  //  appropriately."
  return 0;
}

void stub_pipe_write(const void *buf, size_t len) {
  // nothing, we don't implement reads so no need for writes
}
