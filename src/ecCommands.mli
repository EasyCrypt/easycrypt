(* -------------------------------------------------------------------- *)
open EcSymbols
open EcLocation

(* -------------------------------------------------------------------- *)
exception TopError of EcLocation.t * exn

val toperror_of_exn : ?gloc:EcLocation.t -> exn -> exn

(* -------------------------------------------------------------------- *)
val addidir  : ?system:bool -> string -> unit
val loadpath : unit -> (bool * string) list

(* -------------------------------------------------------------------- *)
type notifier = string -> unit

val set_notifier : notifier -> unit
val get_notifier : unit -> notifier
val notify : EcScope.scope -> ('a, unit, string, unit) format4 -> 'a

(* -------------------------------------------------------------------- *)
val current : unit -> EcScope.scope

(* -------------------------------------------------------------------- *)
val full_check : bool -> int -> string list option -> unit
val process    : EcParsetree.global located -> unit

val undo : int  -> unit
val uuid : unit -> int
val mode : unit -> string

(* -------------------------------------------------------------------- *)
val pp_current_goal : Format.formatter -> unit
val pp_maybe_current_goal : Format.formatter -> unit
