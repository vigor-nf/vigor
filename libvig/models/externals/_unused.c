// Methods that DPDK depends on but are not actually used in symbolic execution.
// This is necessary for building the NFOS, since we can't just have missing linker symbols.
// Signatures are wrong because the linker doesn't care, we just keep the "has return value or not" info.

#ifndef KLEE_VERIFICATION

#include <stdlib.h>

uint64_t TIME; // from hardware models, not DPDK

int __fxstat() { abort(); }

void __libc_fcntl() { abort(); }

void __vsyscall() { abort(); }

void __vsyscall6() { abort(); }

int __xmknod() { abort(); }

int __xstat() { abort(); }

void connect() { abort(); }

void dlerror() { abort(); }

void epoll_create() { abort(); }

void epoll_ctl() { abort(); }

void epoll_wait() { abort(); }

void eventfd() { abort(); }

void fallocate() { abort(); }

void getcwd() { abort(); }

void getdtablesize() { abort(); }

void getegid() { abort(); }

void geteuid() { abort(); }

void getgid() { abort(); }

void getpid() { abort(); }

void inb() { abort(); }

void inl() { abort(); }

void inw() { abort(); }

void ioctl() { abort(); }

void memfd_create() { abort(); }

void mkdir() { abort(); }

void mknod() { abort(); }

void mlock() { abort(); }

void numa_set_localalloc() { abort(); }

void numa_set_preferred() { abort(); }

void openat() { abort(); }

void outb_p() { abort(); }

void outl_p() { abort(); }

void outw_p() { abort(); }

void poll() { abort(); }

void pread64() { abort(); }

void pwrite64() { abort(); }

void pthread_equal() { abort(); }

void pwrite() { abort(); }

void regcomp() { abort(); }

void regexec() { abort(); }

void set_mempolicy() { abort(); }

void siglongjmp() { abort(); }

void timerfd_settime() { abort(); }

void unlinkat() { abort(); }

#endif // !KLEE_VERIFICATION
