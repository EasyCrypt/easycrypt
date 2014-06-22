(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

(* -------------------------------------------------------------------- *)
open EcLocation

(* -------------------------------------------------------------------- *)
exception TopError of EcLocation.t * exn

val toperror_of_exn : ?gloc:EcLocation.t -> exn -> exn

(* -------------------------------------------------------------------- *)
val addidir  : ?system:bool -> ?recursive:bool -> string -> unit
val loadpath : unit -> (bool * string) list

(* -------------------------------------------------------------------- *)
type notifier = string -> unit

val set_notifier : notifier -> unit
val get_notifier : unit -> notifier
val notify : EcScope.scope -> ('a, unit, string, unit) format4 -> 'a

(* -------------------------------------------------------------------- *)
val initialize : boot:bool -> wrapper:(string option) -> unit
val current    : unit -> EcScope.scope

(* -------------------------------------------------------------------- *)
val full_check : bool -> timeout:int -> nprovers:int -> string list option -> unit
val process    : EcParsetree.global located -> unit

val undo : int  -> unit
val uuid : unit -> int
val mode : unit -> string

(* -------------------------------------------------------------------- *)
val pp_current_goal : Format.formatter -> unit
val pp_maybe_current_goal : Format.formatter -> unit

(* -------------------------------------------------------------------- *)
val pragma_verbose : bool -> unit
val pragma_check   : bool -> unit
