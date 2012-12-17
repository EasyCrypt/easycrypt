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

(* --------------------------------------------------------------------- *)
(*           predefined path                                             *)
(* ----------------------------------------------------------------------*)

val id_top       : EcIdent.t
val id_pervasive : EcIdent.t

val p_pervasive  : path
val p_top        : path
val p_int        : path
val p_real       : path
val p_bool       : path
val p_true       : path
val p_false      : path

val p_not        : path
val p_and        : path
val p_or         : path
val p_imp        : path
