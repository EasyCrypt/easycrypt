(* -------------------------------------------------------------------- *)
open Symbols
open Utils
open Maps

(* -------------------------------------------------------------------- *)
type ident = symbol * UidGen.uid
type t     = ident

let create (x : symbol) =
  (x, UidGen.unique ())

let fresh ((x, _) : t) =
  (x, UidGen.unique ())

let name ((x, _) : t) =
  x

let stamp ((_, i) : t) =
  i

(* -------------------------------------------------------------------- *)
module RawMap = Map.Make(struct
  type t = ident
  let  compare = (Pervasives.compare : t -> t -> int)
end)

(* -------------------------------------------------------------------- *)
module Map = struct
  type key  = t
  type 'a t = ((int * 'a) list) SymMap.t

  let empty : 'a t =
    SymMap.empty

  let add ((x, i) : key) (v : 'a) (m : 'a t) =
    SymMap.update (fun p -> (i, v) :: (odfl [] p)) x m

  let byident ((x, i) : key) (m : 'a t) =
    obind (SymMap.tryfind x m) (List.tryassoc i)

  let byname (x : symbol) (m : 'a t) =
    match SymMap.tryfind x m with
    | None | Some []     -> None
    | Some ((_, v) :: _) -> Some v
end
