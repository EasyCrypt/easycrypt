/* -------------------------------------------------------------------- */
#include <sys/types.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <errno.h>

#include <signal.h>
#include <unistd.h>

#include <sys/wait.h>

/* -------------------------------------------------------------------- */
#define ARRAYSIZE(A) (sizeof (A) / sizeof ((A)[0]))

/* -------------------------------------------------------------------- */
static void iprintf_exit(const char *format, ...)
    __attribute__((format(printf, 1, 2)))
    __attribute__((noreturn));

static void iprintf_exit(const char *format, ...) {
    va_list ap;

    va_start(ap, format);
    (void) vfprintf(stderr, format, ap);
    va_end(ap);
    (void) fprintf(stderr, "\n");
    exit(EXIT_FAILURE);
}

/* -------------------------------------------------------------------- */
static void eprintf_exit(const char *format, ...)
    __attribute__((format(printf, 1, 2)))
    __attribute__((noreturn));

static void eprintf_exit(const char *format, ...) {
    va_list ap;

    va_start(ap, format);
    (void) vfprintf(stderr, format, ap);
    va_end(ap);
    (void) fprintf(stderr, ": %s\n", strerror(errno));
    exit(EXIT_FAILURE);
}

/* -------------------------------------------------------------------- */
static int handler_set(int signal, void (*handler)(int)) {    
    struct sigaction sigact;

    memset(&sigact, 0, sizeof(sigact));
    sigact.sa_handler = handler;
    (void) sigemptyset(&sigact.sa_mask);
    return sigaction(signal, &sigact, NULL);
}

/* -------------------------------------------------------------------- */
static int handler_reset(int signal) {
    return handler_set(signal, SIG_DFL);
}

/* -------------------------------------------------------------------- */
static const int csignals[] = { SIGINT, SIGTERM, SIGUSR1, SIGUSR2, SIGCHLD };

/* -------------------------------------------------------------------- */
static void signals_block(void) {
    sigset_t mask;

    (void) sigemptyset(&mask);
    for (size_t i = 0; i < ARRAYSIZE(csignals); ++i)
        sigaddset(&mask, csignals[i]);
    (void) sigprocmask(SIG_BLOCK, &mask, NULL);
}

/* -------------------------------------------------------------------- */
static void signals_unblock(void) {
    sigset_t mask;

    (void) sigemptyset(&mask);
    for (size_t i = 0; i < ARRAYSIZE(csignals); ++i)
        sigaddset(&mask, csignals[i]);
    (void) sigprocmask(SIG_UNBLOCK, &mask, NULL);
}

/* -------------------------------------------------------------------- */
static void signals_wait(void) {
    sigset_t mask;

    (void) sigemptyset(&mask);
    (void) sigprocmask(0, NULL, &mask);
    for (size_t i = 0; i < ARRAYSIZE(csignals); ++i)
        sigdelset(&mask, csignals[i]);
    (void) sigsuspend(&mask);
}

/* -------------------------------------------------------------------- */
static volatile sigset_t signaled;

#define SIGNALED ((sigset_t*) &signaled)

void sighandler(int sig) {
    (void) sigaddset(SIGNALED, sig);
}

/* -------------------------------------------------------------------- */
int main(int argc, char *const *argv) {
    pid_t pid = 1;

    sigemptyset(SIGNALED);

    if (argc-1 == 0)
        iprintf_exit("Usage: %s [COMMAND] <ARGS...>", argv[0]);

    signals_block();

    if ((pid = fork()) < 0)
        eprintf_exit("cannot start a new process (fork(2))");

    if (pid == 0) {
        (void) setpgid(0, 0);
        signals_unblock();
        (void) execvp(argv[1], &argv[1]);
        _exit(127);
    }

    (void) setpgid(pid, 0);

    for (size_t i = 0; i < ARRAYSIZE(csignals); ++i)
        (void) handler_set(csignals[i], sighandler);

    while (1) {
        signals_wait();

        if (sigismember(SIGNALED, SIGCHLD) > 0) {
            int status = 0;

            while (waitpid(pid, &status, 0) < 0) {
                if (errno != EINTR)
                    eprintf_exit("wait(2) failed");
            }

            if (WIFEXITED(status))
                return WEXITSTATUS(status);

            if (WIFSIGNALED(status))
                return 127;

            abort();
        }

        for (size_t i = 0; i < ARRAYSIZE(csignals); ++i) {
            const int sig = csignals[i];
            if (sig != SIGCHLD && sigismember(SIGNALED, sig))
                (void) kill(-pid, sig);
        }

        (void) sigemptyset(SIGNALED);
    }

    return 0;
}
