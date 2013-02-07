(* -------------------------------------------------------------------- *)
open EcMaps

(* -------------------------------------------------------------------- *)
type symbol  = (* private *) string
type qsymbol = (* private *) symbol list * symbol

type symbols = symbol list

(* -------------------------------------------------------------------- *)
val equal : symbol -> symbol -> bool

(* -------------------------------------------------------------------- *)
module Msym : Map.S with type key = symbol
module Ssym : Msym.Set

val pp_symbol  : symbol EcFormat.pp
val pp_qsymbol : qsymbol EcFormat.pp


