#include <dlfcn.h>
#include <klee/klee.h>

void *dlopen(const char *filename, int flags){
  if (flags == (RTLD_LAZY | RTLD_NOLOAD) && filename != NULL) {
    /* "This can be used to test if the object is already resident
       (dlopen() returns NULL if it is not, or the object's handle
       if it is resident)"
       --https://www.man7.org/linux/man-pages/man3/dlopen.3.html
       Vigor is statically linked, so shared library is not already
       loaded, so we return NULL.
    */
    return NULL;
  }
  klee_abort();
}
