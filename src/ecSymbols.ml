(* -------------------------------------------------------------------- *)
open EcMaps

(* -------------------------------------------------------------------- *)
type symbol  = (* private *) string
type qsymbol = (* private *) symbol list * symbol

type symbols = symbol list

let equal : symbol -> symbol -> bool = (=)
let compare : symbol -> symbol -> int = Pervasives.compare

(* -------------------------------------------------------------------- *)
module Msym = Map.Make(struct
  type t = symbol
  let  compare = Pervasives.compare
end)

module Ssym = Msym.Set

(* -------------------------------------------------------------------- *)
module MMsym : sig
  type +'a t

  val empty  : 'a t
  val add    : symbol -> 'a -> 'a t -> 'a t
  val last   : symbol -> 'a t -> 'a option
  val all    : symbol -> 'a t -> 'a list
  val fold   : (symbol -> 'a list -> 'b -> 'b) -> 'a t -> 'b -> 'b
end = struct
  type 'a t = ('a list) Msym.t

  let empty : 'a t = Msym.empty

  let add (x : symbol) (v : 'a) (m : 'a t) =
    Msym.change
      (fun crt -> Some (v :: (EcUtils.odfl [] crt))) x m

  let last (x : symbol) (m : 'a t) =
    match Msym.find_opt x m with
    | None          -> None
    | Some []       -> None
    | Some (v :: _) -> Some v

  let all (x : symbol) (m : 'a t) =
    EcUtils.odfl [] (Msym.find_opt x m)

  let fold f m x = Msym.fold f m x
end

(* -------------------------------------------------------------------- *)
let pp_symbol fmt s = Format.fprintf fmt "%s" s

let rec pp_qsymbol fmt = function
  | ([]    , x) -> Format.fprintf fmt "%s" x
  | (n :: p, x) -> Format.fprintf fmt "%s.%a" n pp_qsymbol (p, x)
