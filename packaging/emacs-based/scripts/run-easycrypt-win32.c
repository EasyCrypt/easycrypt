/* ------------------------------------------------------------------------ */
#if !defined(UNICODE)
# define UNICODE 1
#endif

#include <SDKDDKVer.h>

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

#include <wchar.h>
#include <string.h>

#include <Windows.h>

/* ------------------------------------------------------------------------ */
#define ARRAY_SIZE(A) (sizeof (A) / sizeof ((A)[0]))

/* ------------------------------------------------------------------------ */
void eprintf_exit(LPWSTR format, ...)
{
    LPWSTR buffer = NULL;
    va_list ars  = NULL;
    const int error = GetLastError();

    FormatMessage(FORMAT_MESSAGE_FROM_SYSTEM |
                  FORMAT_MESSAGE_ALLOCATE_BUFFER,
                  NULL, 
                  error,
                  0,
                  (LPWSTR) &buffer, 
                  0, 
                  NULL);

    va_start(ars, format);
    (void) vfwprintf(stderr, format, ars);
    va_end(ars);

    if (buffer == NULL)
        fwprintf(stderr, L": %d\n", error);
    else
        fwprintf(stderr, L": %s\n", buffer);
    (void) fflush(stderr);

    if (buffer != NULL)
        LocalFree(buffer);

    exit(EXIT_FAILURE);
}

/* ------------------------------------------------------------------------ */
#define CMD L"share\\emacs\\bin\\runemacs.exe -l share\\easycrypt\\pg\\emacs.rc --no-init-file --no-site-file --debug-init"

/* ------------------------------------------------------------------------ */
int wmain(int argc, LPWSTR argv[]) {
    HMODULE myself;
    STARTUPINFO si;
    PROCESS_INFORMATION pi;
    DWORD piflags;
    WCHAR cmd[] = CMD;

    (void) argc;
    (void) argv;

    if ((myself = GetModuleHandle(NULL)) != NULL) {
      WCHAR  myname [_MAX_PATH +1];
      WCHAR  mydir  [_MAX_DIR  +1];
      WCHAR  mydrive[_MAX_DRIVE+1];
      WCHAR  myfinal[_MAX_PATH +1];
      DWORD  res   = 0;
      DWORD  envsz = 0;
      DWORD  bufsz = 0;
      LPWSTR opath = NULL;
      LPWSTR npath = NULL;

      res = GetModuleFileName(myself, myname, ARRAY_SIZE(myname));
      if (res > 0 && res < ARRAY_SIZE(myname)) {
        _wsplitpath(myname , mydrive, mydir, NULL, NULL);
        _wmakepath (myfinal, mydrive, mydir, NULL, NULL);
        if (!SetCurrentDirectory(myfinal))
	  eprintf_exit(L"cannot change current directory");
        _wmakepath (myfinal, mydrive, mydir, L"bin", NULL);
        envsz = GetEnvironmentVariable(L"PATH", NULL, 0);
        bufsz = envsz + 1 + wcslen(myfinal) + 1;

        if ((opath = malloc(envsz * sizeof(WCHAR))) == NULL ||
            (npath = malloc(bufsz * sizeof(WCHAR))) == NULL )
	  eprintf_exit(L"memory exhausted");

        wcscpy(npath, myfinal);

        if (envsz > 0) {
          if (GetEnvironmentVariable(L"PATH", opath, envsz) != envsz-1)
	    eprintf_exit(L"cannot recover $PATH");
	  wcscat(npath, L";"); wcscat(npath, opath);
        }

        if (!SetEnvironmentVariable(L"PATH", npath))
	  eprintf_exit(L"cannot set $PATH");
      }
    } else
      eprintf_exit(L"cannot recover module handle");

    ZeroMemory(&si, sizeof (si));
    si.cb = sizeof(si);
    si.dwFlags = STARTF_USESHOWWINDOW | STARTF_USECOUNTCHARS;
    si.wShowWindow = SW_HIDE;
    si.dwXCountChars = 80;
    si.dwYCountChars = 25;

    ZeroMemory(&pi, sizeof(pi));

    piflags  = 0;
    piflags |= CREATE_NEW_PROCESS_GROUP;

    if (!CreateProcess(
          NULL,           // No module name (use command line)
          cmd,            // Command line
          NULL,           // Process handle not inheritable
          NULL,           // Thread handle not inheritable
          FALSE,          // Set handle inheritance to FALSE
          piflags,        // No creation flags
          NULL,           // Use parent's environment block
          NULL,           // Use parent's startin directory 
          &si,            // Pointer to STARTUPINFO structure
          &pi)            // Pointer to PROCESS_INFORMATION structure
       )
    {
        eprintf_exit(L"Cannot create process");
    }

    (void) CloseHandle(pi.hProcess);
    (void) CloseHandle(pi.hThread);

    return 0;
}
