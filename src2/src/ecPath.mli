(* -------------------------------------------------------------------- *)
open EcSymbols

(* -------------------------------------------------------------------- *)
type path = 
  | Pident of EcIdent.t
  | Pqname of path * EcIdent.t

val p_equal : path -> path -> bool
val p_compare : path -> path -> int

(* -------------------------------------------------------------------- *)
val create    : string -> path
val toqsymbol : path -> qsymbol
val basename  : path -> EcIdent.t
val rootname  : path -> EcIdent.t
val extend    : path option -> EcIdent.t -> path
val tolist    : path -> EcIdent.t list 

(* -------------------------------------------------------------------- *)
module Mp : Map.S with type key = path


