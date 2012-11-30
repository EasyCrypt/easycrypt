(* -------------------------------------------------------------------- *)
open EcMaps

(* -------------------------------------------------------------------- *)
type symbol  = (* private *) string
type qsymbol = (* private *) symbol list * symbol

type symbols = symbol list

(* -------------------------------------------------------------------- *)
val equal : symbol -> symbol -> bool

(* -------------------------------------------------------------------- *)
module SymMap : Map.S with type key = symbol
