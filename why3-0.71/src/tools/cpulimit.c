/**************************************************************************/
/*                                                                        */
/*  Copyright (C) 2010-2011                                               */
/*    François Bobot                                                      */
/*    Jean-Christophe Filliâtre                                           */
/*    Claude Marché                                                       */
/*    Andrei Paskevich                                                    */
/*                                                                        */
/*  This software is free software; you can redistribute it and/or        */
/*  modify it under the terms of the GNU Library General Public           */
/*  License version 2.1, with the special exception on linking            */
/*  described in file LICENSE.                                            */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/**************************************************************************/

#include <sys/types.h>
#include <sys/time.h>
#include <time.h>
#include <sys/times.h>
#include <sys/resource.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
#include <sys/wait.h>
#include <signal.h>

int main(int argc, char *argv[]) {
  long timelimit, memlimit;
  int showtime, hidetime;
  struct rlimit res;

  showtime = argc >= 4 && !strncmp("-s",argv[3],3);
  hidetime = argc >= 4 && !strncmp("-h",argv[3],3);

  if (argc < 5 || !(showtime || hidetime)) {
    fprintf(stderr, "usage: %s <time limit in seconds> <virtual memory limit in MiB>\n"
                    "          <show/hide cpu time: -s|-h> <command> <args>...\n\n"
                    "Zero sets no limit (keeps the actual limit)\n", argv[0]);
    return EXIT_FAILURE;
  }

  /* Fork if requested */
  if (showtime) {
      int pid = fork ();

      if (pid == -1) {
          perror("fork");
          exit(EXIT_FAILURE);
      }

      if (pid > 0) {
          int status;
          struct tms tms;
          double time;

          waitpid(pid, &status, 0);

          times(&tms);
          time = (double)((tms.tms_cutime + tms.tms_cstime + 0.0)
                                 / sysconf(_SC_CLK_TCK));
          fprintf(stdout, "why3cpulimit time : %f s\n", time);

          if (WIFEXITED(status)) return WEXITSTATUS(status);
          kill(getpid(),SIGTERM);
      }
  }

  /* get time limit in seconds from command line */
  timelimit = atol(argv[1]);

  if (timelimit > 0) {
    /* set the CPU time limit */
    getrlimit(RLIMIT_CPU,&res);
    res.rlim_cur = timelimit;
    setrlimit(RLIMIT_CPU,&res);
  }

  /* get virtual memory limit in MiB from command line */
  memlimit = atol(argv[2]);

  if (memlimit > 0) {
    /* set the CPU memory limit */
    getrlimit(RLIMIT_AS,&res);
    res.rlim_cur = memlimit * 1024 * 1024;
    setrlimit(RLIMIT_AS,&res);
  }

  if (timelimit > 0 || memlimit > 0) {
    /* do not generate core dumps */
    getrlimit(RLIMIT_CORE,&res);
    res.rlim_cur = 0;
    setrlimit(RLIMIT_CORE,&res);
  }

  /* execute the command */
  execvp(argv[4],argv+4);
  fprintf(stderr, "%s: exec of '%s' failed (%s)\n",
          argv[0],argv[4],strerror(errno));

  return EXIT_FAILURE;

}

