(* Copyright Jeremy Yallop 2007.
   Copyright Grégoire Henry 2011.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

type ('a,'b) either = Left of 'a | Right of 'b

let either_partition (f : 'a -> ('b, 'c) either) (l : 'a list)
    : 'b list * 'c list =
  let rec aux (lefts, rights) = function
    | [] -> (List.rev lefts, List.rev rights)
    | x::xs ->
        match f x with
          | Left l  -> aux (l :: lefts, rights) xs
          | Right r -> aux (lefts, r :: rights) xs
  in aux ([], []) l


module List =
struct
  include List

  let fold_left1 : ('a -> 'a -> 'a) -> 'a list -> 'a
    = fun f l -> match l with
      | x::xs  -> List.fold_left f x xs
      | []     -> invalid_arg "fold_left1"

  let rec fold_right1 : ('a -> 'a -> 'a) -> 'a list -> 'a
    = fun f l -> match l with
      | [x]   -> x
      | x::xs -> f x (fold_right1 f xs)
      | []    -> invalid_arg "fold_right1"

  let rec range from upto =
    let rec aux f t result =
      if f = t then result
      else aux (f+1) t (f::result)
    in if upto < from then raise (Invalid_argument "range")
      else List.rev (aux from upto [])

  let rec last : 'a list -> 'a = function
    | []    -> invalid_arg "last"
    | [x]   -> x
    | _::xs -> last xs

  let concat_map f l =
    let rec aux = function
      | _, [] -> []
      | f, x :: xs -> f x @ aux (f, xs)
    in aux (f,l)

  let concat_map2 (f : 'a -> 'b -> 'c list) (l1 : 'a list) (l2 : 'b list) : 'c list =
    let rec aux = function
      | [], [] -> []
      | x::xs, y :: ys -> f x y @ aux (xs, ys)
      | _ -> invalid_arg "concat_map2"
    in aux (l1, l2)

  let mapn ?(init=0) f =
    let rec aux n = function
      | [] -> []
      | x::xs -> f x n :: aux (n+1) xs in
      aux init

  let rec zip xs ys = match xs, ys with
  | [], [] -> []
  | x::xs, y::ys -> (x, y) :: zip xs ys
  | _, _ -> invalid_arg "List.zip"

  let rec split3 xyzs = match xyzs with
  | [] -> [], [], []
  | (x, y, z) :: xyzs ->
      let xs, ys, zs = split3 xyzs in
      x :: xs, y :: ys, z :: zs

end

module F =
struct
  let id x = x
  let curry f x y = f (x,y)
  let uncurry f (x,y) = f x y
end

module Option =
struct
  let map f = function
    | None -> None
    | Some x -> Some (f x)
end

module DumpAst =
struct
  open Camlp4.PreCast.Ast

  let rec ident = function
    | IdAcc (_, i1, i2) -> "IdAcc ("^ident i1^","^ident i2^")"
    | IdApp (_, i1, i2) -> "IdApp ("^ident i1^","^ident i2^")"
    | IdLid (_, s) -> "IdLid("^s^")"
    | IdUid (_, s) -> "IdUid("^s^")"
    | IdAnt (_, s) -> "IdAnt("^s^")"

  let rec ctyp = function
    | TyLab (_, s, c) -> "TyLab ("^s ^ "," ^ ctyp c ^")"
    | TyDcl (_, s, cs, c2, ccs) -> "TyDcl ("^s ^", [" ^ String.concat ";" (List.map ctyp cs) ^"], "^ctyp c2 ^ ", ["^
        String.concat "," (List.map (fun (c1,c2) -> "(" ^ ctyp c1 ^ ", " ^ ctyp c2 ^ ")") ccs)
        ^ "])"
    | TyObj (_, c, _) -> "TyObj ("^ ctyp c ^ ", ?)"
    | TyOlb (_, s, c) -> "TyOlb ("^s ^ "," ^ ctyp c ^")"
    | TyOf (_, c1, c2) -> "TyOf ("^ ctyp c1 ^ ", " ^ ctyp c2 ^ ")"
    | TyOr (_, c1, c2) -> "TyOr ("^ ctyp c1 ^ ", " ^ ctyp c2 ^ ")"
    | TyRec (_, c) -> "TyRec("^ctyp c^")"
    | TySum (_, c) -> "TySum("^ctyp c^")"
    | TyPrv (_, c) -> "TyPrv("^ctyp c^")"
    | TyMut (_, c) -> "TyMut("^ctyp c^")"
    | TyTup (_, c) -> "TyTup("^ctyp c^")"
    | TyVrnEq (_, c) -> "TyVrnEq("^ctyp c^")"
    | TyVrnSup (_, c) -> "TyVrnSup("^ctyp c^")"
    | TyVrnInf (_, c) -> "TyVrnInf("^ctyp c^")"
    | TyCls (_, i) -> "TyCls("^ident i^")"
    | TyId (_, i) -> "TyId("^ident i^")"
    | TyNil (_) -> "TyNil"
    | TyAli (_, c1, c2) -> "TyAli ("^ ctyp c1 ^ ", " ^ ctyp c2 ^")"
    | TyAny (_) -> "TyAny"
    | TyApp (_, c1, c2) -> "TyApp ("^ ctyp c1 ^ ", " ^ ctyp c2 ^")"
    | TyArr (_, c1, c2) -> "TyArr ("^ ctyp c1 ^ ", " ^ ctyp c2 ^")"
    | TyMan (_, c1, c2) -> "TyMan ("^ ctyp c1 ^ ", " ^ ctyp c2 ^")"
    | TyPol (_, c1, c2) -> "TyPol ("^ ctyp c1 ^ ", " ^ ctyp c2 ^")"
    | TyQuo (_, s) -> "TyQuo("^s^")"
    | TyQuP (_, s) -> "TyQuP("^s^")"
    | TyQuM (_, s) -> "TyQuM("^s^")"
    | TyVrn (_, s) -> "TyVrn("^s^")"
    | TyCol (_, c1, c2) -> "TyCol ("^ ctyp c1 ^ ", " ^ ctyp c2 ^")"
    | TySem (_, c1, c2) -> "TySem ("^ ctyp c1 ^ ", " ^ ctyp c2 ^")"
    | TyCom (_, c1, c2) -> "TyCom ("^ ctyp c1 ^ ", " ^ ctyp c2 ^")"
    | TyAnd (_, c1, c2) -> "TyAnd ("^ ctyp c1 ^ ", " ^ ctyp c2 ^")"
    | TySta (_, c1, c2) -> "TySta ("^ ctyp c1 ^ ", " ^ ctyp c2 ^")"
    | TyVrnInfSup (_, c1, c2) -> "TyVrnInfSup ("^ ctyp c1 ^ ", " ^ ctyp c2 ^")"
    | TyAmp (_, c1, c2) -> "TyAmp ("^ ctyp c1 ^ ", " ^ ctyp c2 ^")"
    | TyOfAmp (_, c1, c2) -> "TyOfAmp ("^ ctyp c1 ^ ", " ^ ctyp c2 ^")"
    | TyPkg (_, mt) -> failwith "first-class modules not supported"
    | TyAnt (_, s) -> "TyAnt("^s^")"
end

module Map = struct

  module type OrderedType = Map.OrderedType

  module type S = sig
    include Map.S
    exception Not_found of key
    val fromList : (key * 'a) list -> 'a t
    val union_disjoint : 'a t list -> 'a t
    val union_disjoint2 : 'a t -> 'a t -> 'a t
  end

  module Make(Ord: OrderedType) = struct

    let nf = Not_found
    exception Not_found of Ord.t

    include Map.Make(Ord)

    let find s m =
      try find s m
      with e when e = nf -> raise (Not_found s)

    let fromList : (key * 'a) list -> 'a t = fun elems ->
      List.fold_right (F.uncurry add) elems empty

    let union_disjoint2 l r =
      fold
	(fun k v r ->
           if mem k r then invalid_arg "union_disjoint"
           else add k v r) l r

    let union_disjoint maps = List.fold_right union_disjoint2 maps empty

  end

end

module Set = struct

  module type OrderedType = Set.OrderedType

  module type S = sig
    include Set.S
    val toList : t -> elt list
    val fromList : elt list -> t
  end

  module Make (Ord : OrderedType) = struct
    include Set.Make(Ord)
    let toList t = fold (fun x acc -> x :: acc) t []
    let fromList elems = List.fold_right add elems empty
  end

end

let random_id length =
  let idchars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'" in
  let nidchars = String.length idchars in
  let s = String.create length in
    for i = 0 to length - 1 do
      s.[i] <- idchars.[Random.int nidchars]
    done;
    s

(* The function used in OCaml to convert variant labels to their
   integer representations.  The formula is given in Jacques
   Garrigue's 1998 ML workshop paper.
*)
let tag_hash s =
  let wrap = 0x40000000 in
  let acc = ref 0 in
  let len = String.length s in
    for i = 0 to len - 1 do
      let c = String.unsafe_get s i in
      let n = Char.code c in
        acc := (223 * !acc + n);
    done;
    acc := !acc land (1 lsl 31 - 1);
    if !acc >= wrap then !acc - (1 lsl 31) else !acc

let _ =
  (* Sanity check to make sure the function doesn't change underneath
     us *)
  assert (tag_hash "premiums" = tag_hash "squigglier");
  assert (tag_hash "deriving" = 398308260);
  assert (tag_hash "Candela" = -1019855834)


(* For type variable renaming *)

let c = "abcdefghijklmnopqrstuvwxyz"

let rec typevar_of_int x =
  assert (x >= 0 && x < 26);
  String.make 1 (c.[x])
