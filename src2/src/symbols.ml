(* -------------------------------------------------------------------- *)
type symbol  = (* private *) string
type qsymbol = (* private *) symbol list * symbol

(* -------------------------------------------------------------------- *)
module SymMap = Map.Make(struct
  type t = symbol
  let  compare = Pervasives.compare
end)
