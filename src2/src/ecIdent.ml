(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils
open EcMaps

(* -------------------------------------------------------------------- *)
type ident = symbol * EcUidgen.uid
type t     = ident

let create (x : symbol) =
  (x, EcUidgen.unique ())

let fresh ((x, _) : t) =
  (x, EcUidgen.unique ())

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

  let allbyname (x : symbol) (m : 'a t) =
    List.map snd (odfl [] (SymMap.tryfind x m))

  let merge m1 m2 = 
    SymMap.merge 
      (fun _ o1 o2 -> 
        match o1 with None -> o2 | Some l1 -> Some ((odfl [] o2) @ l1))
      m1 m2

end

module SMid = EcMaps.StructMake(struct type t = ident let tag = snd end)
module Mid = SMid.M
module Sid = SMid.S
module Hid = SMid.H
