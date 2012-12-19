(* -------------------------------------------------------------------- *)
open EcMaps

(* -------------------------------------------------------------------- *)
type symbol  = (* private *) string
type qsymbol = (* private *) symbol list * symbol

type symbols = symbol list

let equal : symbol -> symbol -> bool = (=)

(* -------------------------------------------------------------------- *)
module Msym = Map.Make(struct
  type t = symbol
  let  compare = Pervasives.compare
end)

module Ssym = Msym.Set
