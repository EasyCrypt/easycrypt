(** Client request correlation ids threaded end-to-end through daemon
    and backend work. See [doc/tooling-protocol.md] § 4. *)

type t

val of_client : string -> t
(** Wrap a client-supplied id. *)

val fresh : unit -> t
(** Generate a fresh daemon-internal id (e.g. for daemon-initiated work). *)

val to_string : t -> string
val equal : t -> t -> bool
val pp : Format.formatter -> t -> unit
