(** Per-user daemon-process discovery: pid + socket files in a known
    location, stale-pid cleanup, single-acquirer locking. Used by
    [ecd daemon] to advertise a live instance and by clients
    (REPL/TUI/LSP/MCP) to find one. See [doc/tooling-poc-plan.md]
    Phase 2 — daemon discovery. *)

type acquired = {
  pid_file : string;
  socket_path : string;
}

type acquire_result =
  | Acquired of acquired
  | Already_running of { pid : int; socket : string option }

val runtime_dir : unit -> string
(** Per-user runtime directory ([XDG_RUNTIME_DIR] when set, else
    [$TMPDIR/easycrypt-daemon-<uid>/], else [/tmp/...]). Created if
    missing with mode 0700. *)

val pid_file : ?label:string -> unit -> string
(** Path to the lock/pid file for [label] (default: ["default"]). *)

val pid_alive : int -> bool
(** Best-effort liveness probe via [kill 0]. Returns [true] if a
    process owns the pid (even if owned by another user). *)

val acquire : ?label:string -> socket_path:string -> unit -> acquire_result
(** Take the discovery lock for [label]. If an existing pid file
    points at a live process, returns [Already_running]; otherwise
    removes any stale file and writes our pid + socket path,
    returning [Acquired]. *)

val release : ?label:string -> unit -> unit
(** Remove the pid file for [label]. Idempotent. *)

val read : ?label:string -> unit -> (int * string option) option
(** Read [label]'s pid file: [Some (pid, socket_path_opt)] when
    present and parseable, [None] when absent or malformed. Does
    not probe liveness. *)
