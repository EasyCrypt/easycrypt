/* ------------------------------------------------------------------------ */
#if defined(__WIN32__)
#include <SDKDDKVer.h>

#include <stdlib.h>
#include <Windows.h>

int wmain(int argc, LPWSTR argv[]) {
  (void) argc;
  (void) argv;
  abort();
}
#else
# include "unix/callprover.c"
#endif
