(* -------------------------------------------------------------------- *)
open EcMaps

(* -------------------------------------------------------------------- *)
type symbol  = (* private *) string
type qsymbol = (* private *) symbol list * symbol

type symbols = symbol list

let equal : symbol -> symbol -> bool = (=)

(* -------------------------------------------------------------------- *)
module SymMap = Map.Make(struct
  type t = symbol
  let  compare = Pervasives.compare
end)
