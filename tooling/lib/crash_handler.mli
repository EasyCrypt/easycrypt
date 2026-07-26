(** Signal-handler crash log. Installs handlers for SIGSEGV /
    SIGABRT / SIGFPE / SIGBUS / SIGILL that try to write a crash
    log before re-raising. Best-effort — OCaml runtime state may
    be inconsistent during signal handling, especially for
    C-level crashes; we capture what we can.

    Crash log location: [~/.cache/easycrypt-daemon-crashes/<timestamp>.log]
    by default; override via [?dir]. Created on first install.

    The handler attempts:
    1. Flush stderr.
    2. Write signal info + OCaml backtrace (if [Printexc.record_backtrace]
       was set) to the crash log file.
    3. Re-raise the signal so the process actually dies.

    Idempotent: calling [install] multiple times is safe; later calls
    update [dir] if provided. *)

val install : ?dir:string -> unit -> unit
(** Install crash handlers. Records the install dir for later
    crash-log writes; creates the dir (mode 0700) if missing. *)

val crash_dir : unit -> string
(** Return the configured crash-log directory. *)
