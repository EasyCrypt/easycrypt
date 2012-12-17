(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
module Map = struct
  module type OrderedType = Why3.Stdlib.Map.OrderedType

  module type S = sig
    include Why3.Stdlib.Map.S

    val update : ('a -> 'a) -> key -> 'a t -> 'a t
    val to_stream : 'a t -> (key * 'a) Stream.t
    val pp : key EcFormat.pp -> 'a EcFormat.pp -> ('a t) EcFormat.pp
  end

  module Make(O : OrderedType) : S with type key = O.t = struct
    include Why3.Stdlib.Map.Make(O)

    let update f (k : key) (m : 'a t) =
      change (omap^~ f) k m

    let to_stream (m : 'a t) =
      let next =
        let enum = ref (start_enum m) in
          fun (_ : int) ->
            let aout = val_enum !enum in
              enum := next_enum !enum;
              aout
      in
        Stream.from next

    let pp pp_key pp_value fmt m =
      let pp fmt (k, v) =
        Format.fprintf fmt "%a = %a" pp_key k pp_value v
      in
        if is_empty m then
          Format.fprintf fmt "{}"
        else begin
          let pp =
            let first = ref true in
              fun k v ->
                if not !first then
                  Format.fprintf fmt "@,%a" pp (k, v)
                else begin
                  Format.fprintf fmt "%a" pp (k, v);
                  first := false
                end
          in
            Format.fprintf fmt "{@,@[<v 2>  %a@]@,}"
              (fun fmt -> iter pp) m
        end
  end
end

(* -------------------------------------------------------------------- *)
module MakeMSH (X : Why3.Stdlib.TaggedType) : sig
  module M : Map.S with type key = X.t
  module S : M.Set
  module H : Why3.Exthtbl.Hashtbl.S with type key = X.t
end = struct
  module T = Why3.Stdlib.OrderedHashed(X)
  module M = Map.Make(T)
  module S = M.Set
  module H = Why3.Exthtbl.Hashtbl.Make(T)
end

(* -------------------------------------------------------------------- *)
module Int = struct
  type t = int
  let compare = (Pervasives.compare : t -> t -> int)
  let equal (x : t) (y : t) = (x = y)
end

module Mint = Map.Make(Int)
module Sint = Mint.Set

(* -------------------------------------------------------------------- *)
module Mstr = Map.Make(String)
module Sstr = Mstr.Set

(* -------------------------------------------------------------------- *)
module PTree : sig
  type +'a t

  val empty  : 'a t
  val lookup : int -> 'a t -> 'a option
  val insert : int -> 'a -> 'a t -> 'a t
  val merge  : 'a t -> 'a t -> 'a t
end = struct
  (* See ``Fast Mergeable Integer EcMaps'' (C. Okasaki / A. Gill) *)

  type +'a t =
    | Empty
    | Branch of int * int * 'a t * 'a t
    | Leaf   of int * 'a

  let (|~) = (lor )
  let (&~) = (land)
  let (^~) = (lxor)

  let empty = Empty

  let lookup (k : int) (m : 'a t) =
    let rec lookup = function
      | Empty               -> None
      | Leaf (i, v)         -> if i == k then Some v else None
      | Branch (_, m, l, r) -> lookup (if m &~ k == 0 then l else r)
    in
      lookup m

  let join (p1, t1) (p2, t2) =
    let bb = (p1 ^~ p2) &~ (- (p1 ^~ p2)) in
      if   p1 &~ bb == 0
      then Branch (p1 &~ (bb-1), bb, t1, t2)
      else Branch (p2 &~ (bb-1), bb, t2, t1)

  let insert (k : int) (v : 'a) (m : 'a t) =
    let rec insert = function
      | Empty -> Leaf (k, v)
      | Leaf (i, _) as m ->
          if   i == k
          then Leaf (i, v)
          else join (i, m) (k, Leaf (k, v))
      | Branch (p, mk, l, r) as m ->
          if   (k &~ (mk-1)) == p
          then if   k &~ mk == 0
               then Branch (p, mk, insert l, r)
               else Branch (p, mk, l, insert r)
          else join (k, Leaf (k, v)) (p, m)
    in
      insert m

  let merge (m1 : 'a t) (m2 : 'a t) =
    let rec merge = function
      | (Empty, m)       | (m, Empty)       -> m
      | (Leaf (k, v), m) | (m, Leaf (k, v)) -> insert k v m

      | ((Branch (p1, mk1, l1, r1) as m1),
         (Branch (p2, mk2, l2, r2) as m2)) ->

        match compare mk1 mk2 with
          | 0 -> if   p1 == p2
                 then Branch (mk1, p1, merge (l1, l2), merge (r1, r2))
                 else join (p1, m1) (p2, m2)

          | n when n < 0 -> merge (m2, m1)

          | _ -> 
              if   (p1 &~ (mk2-1)) == p2
              then if   p2 &~ mk2 == 0
                   then Branch (p2, mk2, merge (m1, l1), l2)
                   else Branch (p2, mk2, l1, merge (m1, l2))
              else join (p1, m1) (p2, m2)
    in
      merge (m1, m2)
end

(* -------------------------------------------------------------------- *)
module UnionFind : sig
  type t

  val create : unit -> t
  val find   : t -> int -> int
  val union  : t -> int -> int -> unit
end = struct
  type m = (int ref * int) PTree.t
  type t = m ref

  let create () =
    ref PTree.empty

  let xfind =
    let rec find i ri rs m =
      match PTree.lookup i m with
        | None         -> (i, ri, rs)
        | Some (r, rk) -> if   !r == i
                          then (i, ri, rs)
                          else find !r rk (r :: rs) m
    in
      fun (m : m) (i : int) ->
        let (i, ri, rs) = find i 0 [] m in
          List.iter (fun r -> r := i) rs; (i, ri)

  let find (m : t) (i : int)=
    fst (xfind !m i)

  let union (m : t) (i : int) (j : int) =
    let i, ri = xfind !m i in
    let j, rj = xfind !m j in
      if i <> j then begin
        if ri < rj then
          m := PTree.insert i (ref j, ri) !m
        else if ri > rj then
          m := PTree.insert j (ref i, rj) !m
        else begin
          m := PTree.insert j (ref j, rj+1) !m;
          m := PTree.insert i (ref j, ri  ) !m
        end
      end
end

(* -------------------------------------------------------------------- *)
module type Tagged = sig
  type t
  val tag : t -> int
end

module type OrderedHash = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module OrderedHash (X : Tagged) = struct 
  type t = X.t
  let hash = X.tag
  let equal t1 t2 = X.tag t1 == X.tag t2 
  let compare t1 t2 = X.tag t1 - X.tag t2
end

module StructMake (X : Tagged) = struct
  module T = OrderedHash(X)
  module M = Map.Make(T)
  module S = Set.Make(T)
  module H = Hashtbl.Make(T)
end
