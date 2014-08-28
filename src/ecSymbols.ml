(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

(* -------------------------------------------------------------------- *)
type symbol  = string
type qsymbol = symbol list * symbol
type msymbol = (symbol * msymbol list) list

let sym_equal   : symbol -> symbol -> bool = (=)
let sym_compare : symbol -> symbol -> int  = Pervasives.compare

(* -------------------------------------------------------------------- *)
module SymCmp = struct
  type t = symbol
  let compare = (Pervasives.compare : t -> t -> int)
end

module Msym = EcMaps.Map.Make(SymCmp)
module Ssym = EcMaps.Set.MakeOfMap(Msym)

(* -------------------------------------------------------------------- *)
module MMsym : sig
  type +'a t

  val empty  : 'a t
  val add    : symbol -> 'a -> 'a t -> 'a t
  val last   : symbol -> 'a t -> 'a option
  val all    : symbol -> 'a t -> 'a list
  val fold   : (symbol -> 'a list -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val map_at : ('a list -> 'a list) -> symbol -> 'a t -> 'a t
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

  let map_at f (x : symbol) (m : 'a t) =
    Msym.change
      (fun v ->
        match f (EcUtils.odfl [] v) with
        | [] -> None
        | v  -> Some v)
      x m
end

(* -------------------------------------------------------------------- *)
let pp_symbol fmt s = Format.fprintf fmt "%s" s

let rec string_of_qsymbol = function
  | ([]    , x) -> Printf.sprintf "%s" x
  | (n :: p, x) -> Printf.sprintf "%s.%s" n (string_of_qsymbol (p, x))

let rec pp_qsymbol fmt qn =
  Format.fprintf fmt "%s" (string_of_qsymbol qn)

let rec string_of_msymbol (mx : msymbol) =
  match mx with
  | [] ->
      ""

  | [(x, [])] ->
      x

  | [(x, args)] ->
      Printf.sprintf "%s(%s)"
        x (String.concat ", " (List.map string_of_msymbol args))

  | nm :: x ->
      Printf.sprintf "%s.%s"
        (string_of_msymbol [nm])
        (string_of_msymbol x)

let pp_msymbol fmt x =
  Format.fprintf fmt "%s" (string_of_msymbol x)
