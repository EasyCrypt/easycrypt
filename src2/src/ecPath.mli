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

(* -------------------------------------------------------------------- *)
module Mp : Map.S with type key = path
