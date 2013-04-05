(* -------------------------------------------------------------------- *)
open EcSymbols
open EcLocation

(* -------------------------------------------------------------------- *)
exception TopError of EcLocation.t * exn

val toperror_of_exn : exn -> exn

(* -------------------------------------------------------------------- *)
type info =
| GI_AddedType      of symbol
| GI_AddedAxiom     of symbol
| GI_AddedOperator  of symbol
| GI_AddedPredicate of symbol
| GI_Goal           of EcScope.proof_uc

(* -------------------------------------------------------------------- *)
val addidir    : string -> unit
val full_check : bool -> int -> string list option -> unit

val process : EcParsetree.global located -> info list 

val undo    : int -> info list
val uuid    : unit -> int
