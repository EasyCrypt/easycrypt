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

(* -------------------------------------------------------------------- *)


let pp_symbol fmt s = Format.fprintf fmt "%s" s

let rec pp_qsymbol fmt = function
  | ([]    , x) -> Format.fprintf fmt "%s" x
  | (n :: p, x) -> Format.fprintf fmt "%s.%a" n pp_qsymbol (p, x)
