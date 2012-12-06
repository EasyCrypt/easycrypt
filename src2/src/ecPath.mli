(* -------------------------------------------------------------------- *)
open EcSymbols

(* -------------------------------------------------------------------- *)
type path =
  | Pident of EcIdent.t
  | Pqname of path * EcIdent.t

val equal : path -> path -> bool

(* -------------------------------------------------------------------- *)
val create    : string -> path
val toqsymbol : path -> qsymbol
val basename  : path -> EcIdent.t
val extend    : path option -> EcIdent.t -> path

(* -------------------------------------------------------------------- *)
module Mp : Map.S with type key = path
