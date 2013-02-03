(* -------------------------------------------------------------------- *)
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
type path = 
  | Pident of EcIdent.t
  | Pqname of path * EcIdent.t

type xpath = path * xpath list

val p_equal : path -> path -> bool
val p_compare : path -> path -> int

val p_equal_complex : xpath -> xpath -> bool

(* -------------------------------------------------------------------- *)
val create    : string -> path
val toqsymbol : path -> qsymbol
val basename  : path -> EcIdent.t
val rootname  : path -> EcIdent.t
val extend    : path option -> EcIdent.t -> path
val concat    : path -> path -> path
val tolist    : path -> EcIdent.t list 
val tostring  : path -> string


(* -------------------------------------------------------------------- *)
module Mp : Map.S with type key = path
module Sp : Mp.Set with type elt = path
