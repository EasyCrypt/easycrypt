(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils
open EcMaps

(* -------------------------------------------------------------------- *)
type ident = symbol * EcUidgen.uid
type t     = ident

let create (x : symbol) =
  (x, EcUidgen.unique ())

let mk (x : symbol) (i : EcUidgen.uid) =
  (x, i)

let fresh ((x, _) : t) =
  (x, EcUidgen.unique ())

let name ((x, _) : t) =
  x

let stamp ((_, i) : t) =
  i

let pp_ident fmt ((x, i) : t) =
  Format.fprintf fmt "%s/%d" x i

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
    SymMap.setdfl (fun p -> (i, v) :: (odfl [] p)) x m

  let byident ((x, i) : key) (m : 'a t) =
    obind (SymMap.tryfind x m) (List.tryassoc i)

  let byname (x : symbol) (m : 'a t) =
    match SymMap.tryfind x m with
    | None | Some []     -> None
    | Some ((i, v) :: _) -> Some (mk x i, v)

  let allbyname (x : symbol) (m : 'a t) =
    List.map (fst_map (mk x)) (odfl [] (SymMap.tryfind x m))

  let update ((n, i) : key) (f : 'a -> 'a) (m : 'a t) =
    let rec update1 (xs : (int * 'a) list) =
      match xs with
      | [] -> []
      | (i', v) :: xs when i = i' -> (i', f v) :: xs
      | x :: xs -> x :: (update1 xs)
    in
      if SymMap.mem n m then
        SymMap.setdfl
          (function None -> [] | Some xs -> update1 xs) n m
      else
        m

   let merge m1 m2 = 
     SymMap.merge 
       (fun _ o1 o2 -> 
         match o1 with None -> o2 | Some l1 -> Some ((odfl [] o2) @ l1))
       m1 m2

   open EcFormat

   let pp ?(align = false) pp_value fmt (m : 'a t) =
     let pp_key =
       match align with
       | false -> pp_string
       | true  -> begin
         let i =
           SymMap.fold (fun x _ j -> max (String.length x) j) m 0
         in
           fun fmt s -> Format.fprintf fmt "%.*s" i s
       end
     in

     let pp fmt bindings =
       pp_list ~pre:"[" ~pst:"]"
         (pp_pair pp_int pp_value) fmt bindings
     in
       SymMap.pp pp_key pp fmt m
end

(* -------------------------------------------------------------------- *)
module SMid = EcMaps.StructMake(struct type t = ident let tag = snd end)

module Mid = SMid.M
module Sid = SMid.S
module Hid = SMid.H
