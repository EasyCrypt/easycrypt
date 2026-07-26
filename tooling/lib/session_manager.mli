(** Per-LSP-connection session manager — owns a
    [(project_root → ProjectSession)] map. Each [ProjectSession] is
    a primary [Proof_state.t] + a sibling [analyze_session]
    ([Ec_llm_session.t]) with project-specific load paths.

    URI → project_root resolution uses [EcOptions.find_project_file]
    (the same upward walk EC's `Ec.main` runs); URIs without an
    [easycrypt.project] up-tree are keyed by the file's containing
    directory (synthetic project — bounded one session per loose
    directory).

    UPSTREAM § 14 / doc/session-model.md — initial-beta scope:
    spawn-on-first-access, close-on-connection-close, hot-reload via
    [invalidate_project]. LRU eviction, idle timeout, master-toggle
    deferred to post-beta. *)

type t

(** Allocate a manager bound to [conn_sw]. Sessions live under that
    switch and are closed when the switch ends. [connection_label]
    is used to prefix per-session labels so logs / transcripts
    distinguish projects. *)
val create
  :  sw:Eio.Switch.t
  -> connection_label:string
  -> t

(** Close all live sessions immediately (proof + analyze for each
    project). Idempotent. The owning switch's cleanup also covers
    this; [close] is here for explicit teardown ahead of switch
    exit. *)
val close : t -> unit

(** Resolve a URI to its project's [Proof_state.t]. First call for
    a project_root spawns the primary EC subprocess; subsequent
    calls return the cached value.

    [sw] is the manager's switch (used for the spawn). For URIs
    without an [easycrypt.project] up-tree, the file's containing
    directory is used as a synthetic project_root. *)
val proof_state_for
  :  t
  -> sw:Eio.Switch.t
  -> uri:string
  -> Proof_state.t

(** Resolve a URI to its project's analyze [Ec_llm_session.t].
    Spawns on first access, mirroring [proof_state_for]. The
    analyze session shares the project's load paths so
    publishDiagnostics sees the same context as the primary. *)
val analyze_session_for
  :  t
  -> sw:Eio.Switch.t
  -> uri:string
  -> Ec_llm_session.t

(** Send SIGINT to the in-flight tactic on the URI's project's
    primary session. Lock-free; mirrors [Proof_state.cancel_in_flight]
    semantics. No-op if the URI doesn't yet have a session. *)
val cancel_in_flight : t -> uri:string -> unit

(** Invalidate (close + drop from cache) the session(s) at
    [project_root]. Next [proof_state_for] / [analyze_session_for]
    call for a URI under that root spawns a fresh session. Used
    by the file-watcher hot-reload path on [easycrypt.project]
    changes. *)
val invalidate_project : t -> project_root:string -> unit

(** Best-effort: resolve the [project_root] for a URI without
    spawning a session. Returns [None] only if the URI cannot be
    parsed as a file path (synthetic-project fallback always
    yields a key for valid file URIs). Used by clients (vscode)
    that want to know the project root before opening the file. *)
val project_root_for : t -> uri:string -> string option
