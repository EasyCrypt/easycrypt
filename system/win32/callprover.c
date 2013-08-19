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
void eprintf_exit(LPWSTR format, ...)
{
    LPWSTR buffer = NULL;
    va_list args  = NULL;
    const int error = GetLastError();

    FormatMessage(FORMAT_MESSAGE_FROM_SYSTEM |
                  FORMAT_MESSAGE_ALLOCATE_BUFFER,
                  NULL, 
                  error,
                  0,
                  (LPWSTR) &buffer, 
                  0, 
                  NULL);

    va_start(args, format);
    (void) vfwprintf(stderr, format, args);
    va_end(args);

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
static DWORD pid = -1;

BOOL WINAPI sighandler(DWORD sig) {
    DWORD mypid = pid;

    if (mypid > 0 && (sig == CTRL_C_EVENT || sig == CTRL_BREAK_EVENT)) {
        (void) GenerateConsoleCtrlEvent(CTRL_BREAK_EVENT, pid);
        return TRUE;
    }
    return FALSE;
}

/* ------------------------------------------------------------------------ */
static LPWSTR create_command(int argc, LPWSTR argv[]) {
    size_t size = 0u;
    LPWSTR cmd  = NULL;

    for (size_t i = 0u; i < (size_t) argc; ++i)
        size += wcslen(argv[i]);
    size += 3 * argc + 1;

    if ((cmd = malloc(size * sizeof(WCHAR))) == NULL)
        return NULL;

    *cmd = L'\0';
    for (size_t i = 0u; i < (size_t) argc; ++i) {
        if (i != 0u) wcscat(cmd, L" ");
        wcscat(cmd, L"\"");
        wcscat(cmd, argv[i]);
        wcscat(cmd, L"\"");
    }

    return cmd;
}

/* ------------------------------------------------------------------------ */
int wmain(int argc, LPWSTR argv[]) {
    STARTUPINFO si;
    PROCESS_INFORMATION pi;
    DWORD status = EXIT_FAILURE;
    DWORD piflags;
    LPWSTR cmd = NULL;

    if (argc-1 == 0) {
        fwprintf(stderr, L"Usage: %s [PROGRAM] <ARGS...>\n", argv[0]);
        return EXIT_FAILURE;
    }

    if ((cmd = create_command(argc-1, &argv[1])) == NULL)
        eprintf_exit(L"Cannot create full command line");

    ZeroMemory(&si, sizeof (si));
    si.cb = sizeof(si);
    si.dwFlags = STARTF_USESHOWWINDOW | STARTF_USECOUNTCHARS;
    si.wShowWindow = SW_HIDE;
    si.dwXCountChars = 80;
    si.dwYCountChars = 25;

    ZeroMemory(&pi, sizeof(pi));

    piflags  = 0;
    piflags |= CREATE_NEW_PROCESS_GROUP;
    piflags |= CREATE_SUSPENDED;

    (void) SetConsoleCtrlHandler(NULL, FALSE);

    if(!CreateProcess(
          NULL,           // No module name (use command line)
          cmd,            // Command line
          NULL,           // Process handle not inheritable
          NULL,           // Thread handle not inheritable
          FALSE,          // Set handle inheritance to FALSE
          piflags,        // No creation flags
          NULL,           // Use parent's environment block
          NULL,           // Use parent's starting directory 
          &si,            // Pointer to STARTUPINFO structure
          &pi)            // Pointer to PROCESS_INFORMATION structure
       )
    {
        eprintf_exit(L"Cannot create process");
    }

    pid = pi.dwProcessId;
    if (!SetConsoleCtrlHandler(&sighandler, TRUE))
        eprintf_exit(L"Cannot set CTRL handler");

    (void) ResumeThread(pi.hThread);
    (void) WaitForSingleObject(pi.hProcess, INFINITE);

    (void) SetConsoleCtrlHandler(&sighandler, FALSE);
    pid = -1;

    (void) GetExitCodeProcess(pi.hProcess, &status);

    (void) CloseHandle(pi.hProcess);
    (void) CloseHandle(pi.hThread);

    return status;
}
