/**************************************************************************/
/*                                                                        */
/*  Copyright (C) 2008-2010                                               */
/*    Dillon PARIENTE 2008                                                */
/*    Claude MARCHE 2010                                                  */
/*                                                                        */
/*  This software is free software; you can redistribute it and/or        */
/*  modify it under the terms of the GNU Library General Public           */
/*  License version 2, with the special exception on linking              */
/*  described in file LICENSE.                                            */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/**************************************************************************/

/* $Id: cpulimit-win.c,v 1.3 2009-12-09 08:28:00 nrousset Exp $ */

#include <windows.h>
#include <stdio.h>
#include <errno.h>

int main(int argc, char *argv[]) {
  STARTUPINFO si;
  PROCESS_INFORMATION pi;
  int i;
  unsigned ex;
  unsigned long s = 0; // length of args after concat
  char * p; // command line parameter
  ZeroMemory(&si, sizeof(si));
  si.cb = sizeof(si);
  ZeroMemory(&pi, sizeof(pi));
  if (argc < 3) {
    printf("Usage: %s <time limit in seconds> <command>\n", argv[0]);
    return -1;
  }
  // concats argv[2..] into a single command line parameter
  for (i = 2; i < argc; i++)
    s += strlen(argv[i]) + 1;
  // CreateProcess does not allow more than 32767 bytes for command line parameter
  if (s > 32767) {
    printf("%s: Error: parameter's length exceeds CreateProcess limits\n", argv[0]);
    return -1;
  }
  p = (char*) malloc(s);
  if (p == NULL) {
    printf("%s: Error: when allocating %d bytes in memory\n", argv[0], (int) s);
    return -1;
  }
  *p = '\0';
  for (i = 2; i < argc; i++) {
    strncat(p, argv[i], strlen(argv[i]));
    if (i < argc - 1) strcat(p, " ");
  }
  // launches "child" process with command line parameter
  if (!CreateProcess(NULL, p, NULL, NULL, FALSE, 0, NULL, NULL, &si, &pi)) {
    printf( "%s: Error: failed when launching <%s>\n", argv[0], p);
    return -1;
  }
  // waits, terminates and frees handles and malloc
  int w = WaitForSingleObject(pi.hProcess, 1000 * atoi(argv[1]));
  TerminateProcess(pi.hProcess, 10);
  GetExitCodeProcess(pi.hProcess, (LPDWORD) &ex);
  CloseHandle(pi.hProcess);
  CloseHandle(pi.hThread);
  free(p);
  if (w == WAIT_TIMEOUT) return 152;
  return ex;
}

// How to compile under Cygwin (needs make, gcc and win32api):
//                 gcc -Wall -o cpulimit cpulimit.c
