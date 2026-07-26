(** Stable sentence identifiers. Opaque to clients; comparison is equality
    only. See [doc/tooling-protocol.md] § 3. *)

type t

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int
val to_string : t -> string

val of_string : string -> t
(** Deserialize from a wire-encoded sid (the [to_string] inverse).
    Opaque to validation: malformed input still produces a [t] that
    won't equal any real sid, so equality lookups simply miss. *)

val pp : Format.formatter -> t -> unit

val of_hash_and_path : hash:string -> path:string -> t
(** Real construction: content hash + structural path. Used by the
    splitter once the containing-theory/section walker lands
    (Phase 2 full). *)

val of_source : string -> t
(** PoC v0 construction: MD5 content-hash of the source substring.
    Stable under whitespace edits only if callers pre-normalise —
    the daemon's splitter is expected to feed already-trimmed
    substrings from addition 1's PARSE-JSON output. Known v0
    limitation: two sentences with identical source text collide
    on the same id; `revert_to` resolves to the latest exec of
    that content. Full protocol § 3 (content-hash + structural
    path) lands when the theory/section walker does. *)

val stub_of_int : int -> t
(** Stub construction for tests and smoke flows. Not for production use. *)
