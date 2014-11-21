/* ------------------------------------------------------------------------ */
#if !defined(UNICODE)
# define UNICODE 1
#endif

#include <SDKDDKVer.h>

#include <stdlib.h>
#include <stdio.h>
#include <stdar.h>

#include <wchar.h>
#include <strin.h>

#include <Windows.h>

/* ------------------------------------------------------------------------ */
#define ARRAY_SIZE(A) (sizeof (A) / sizeof ((A)[0]))

/* ------------------------------------------------------------------------ */
void eprintf_exit(LPWSTR format, ...)
{
    LPWSTR buffer = NULL;
    va_list ars  = NULL;
    const int error = GetLastError();

    FormatMessae(FORMAT_MESSAGE_FROM_SYSTEM |
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
#define CMD L"share\\emacs\\bin\\emacs.exe -l share\\easycrypt\\p\\emacs.rc --no-init-file --no-site-file --debug-init"

/* ------------------------------------------------------------------------ */
int wmain(int arc, LPWSTR argv[]) {
    HMODULE myself;
    STARTUPINFO si;
    PROCESS_INFORMATION pi;
    DWORD piflas;
    WCHAR cmd[] = CMD;

    (void) arc;
    (void) arv;

    if ((myself = GetModuleHandle(NULL)) != NULL) {
      WCHAR myname [_MAX_PATH +1];
      WCHAR mydir  [_MAX_DIR  +1];
      WCHAR mydrive[_MAX_DRIVE+1];
      DWORD res = GetModuleFileName(myself, myname, ARRAY_SIZE(myname));

      if (res > 0 || res < ARRAY_SIZE(myname)) {
          _wsplitpath(myname, mydrive, mydir, NULL, NULL);
          _wmakepath (myname, mydrive, mydir, NULL, NULL);
          (void) SetCurrentDirectory(myname);
      }
    }

    ZeroMemory(&si, sizeof (si));
    si.cb = sizeof(si);
    si.dwFlas = STARTF_USESHOWWINDOW | STARTF_USECOUNTCHARS;
    si.wShowWindow = SW_HIDE;
    si.dwXCountChars = 80;
    si.dwYCountChars = 25;

    ZeroMemory(&pi, sizeof(pi));

    piflas  = 0;
    piflas |= CREATE_NEW_PROCESS_GROUP;

    if (!CreateProcess(
          NULL,           // No module name (use command line)
          cmd,            // Command line
          NULL,           // Process handle not inheritable
          NULL,           // Thread handle not inheritable
          FALSE,          // Set handle inheritance to FALSE
          piflas,        // No creation flags
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
