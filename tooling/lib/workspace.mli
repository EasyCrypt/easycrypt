(** Minimal workspace: the daemon-wide set of open documents plus the
    authoritative load path fed to every `ec llm` subprocess. Phase 2
    scope per `doc/tooling-poc-plan.md`. Future promotions (cache,
    symbol index, discovery) land in Phase 4 on top of this type —
    the callers should stay on the API defined here.

    The workspace is a pure registry: it holds no session state and
    does no I/O beyond the splitter calls its clients drive. All
    writes are from the daemon's single event loop, so no internal
    locking is provided. *)

type t

val make : load_path:string list -> t
(** [make ~load_path] creates an empty workspace with the given
    ordered list of `-I`/`-R` directories. *)

val load_path : t -> string list
val set_load_path : t -> string list -> unit
(** Replaces the authoritative load path. The daemon should tear
    down any running sessions before changing this since existing
    subprocesses were spawned with the old path. *)

(** {1 Document lifecycle} *)

val open_document : t -> Document.t -> unit
(** [didOpen]. Fails via an assertion if the URI is already open —
    the daemon should not multiplex didOpen events for the same
    document. *)

val update_document :
  t -> Document.t -> Document.diff option
(** [didChange]. Replaces the stored document at the same URI,
    returning [Some diff] against the prior version, or [None] if
    the URI was unknown (which the daemon treats as a protocol
    error). *)

val close_document : t -> uri:string -> unit
(** [didClose]. No-op if the URI wasn't open. *)

val get : t -> uri:string -> Document.t option
val documents : t -> Document.t list

val uris : t -> string list
