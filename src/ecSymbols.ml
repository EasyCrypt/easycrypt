(* -------------------------------------------------------------------- *)
open EcMaps

(* -------------------------------------------------------------------- *)
type symbol  = string
type qsymbol = symbol list * symbol
type msymbol = (symbol * msymbol) list

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

  val dump :
       name:string
    -> (EcDebug.ppdebug -> 'a -> unit)
    -> EcDebug.ppdebug
    -> 'a t
    -> unit
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

  let dump ~name valuepp pp (m : 'a t) =
    let keyprinter k v =
      match v with
      | [] -> Printf.sprintf "%s (empty)" k
      | _  -> k
            
    and valuepp pp (x, vs) =
      match vs with
      | [] -> ()
      | _  ->
          EcDebug.onhlist pp
            (Printf.sprintf "%d binding(s)" (List.length vs))
            (fun pp v ->
              EcDebug.onhlist pp x valuepp [v])
            vs
    in
      Msym.dump ~name keyprinter valuepp pp m
end

(* -------------------------------------------------------------------- *)
let pp_symbol fmt s = Format.fprintf fmt "%s" s

let rec string_of_qsymbol = function
  | ([]    , x) -> Printf.sprintf "%s" x
  | (n :: p, x) -> Printf.sprintf "%s.%s" n (string_of_qsymbol (p, x))

let rec pp_qsymbol fmt qn =
  Format.fprintf fmt "%s" (string_of_qsymbol qn)
