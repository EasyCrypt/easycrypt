(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Stdlib

(* useful combinators *)

let ($) f x = f x
let (|>) x f = f x

let const f _ = f

let const2 f _ _ = f

let const3 f _ _ _ = f

let flip f x y = f y x

let cons f acc x = (f x)::acc

(* useful option combinators *)

let of_option = function None -> assert false | Some x -> x

let default_option d = function None -> d | Some x -> x

let option_map f = function None -> None | Some x -> Some (f x)

let option_apply d f = function None -> d | Some x -> f x

let option_fold f d = function None -> d | Some x -> f d x

let option_iter f = function None -> () | Some x -> f x

let option_map2 f x y = match x,y with
  | None, None -> None
  | Some x, Some y -> Some (f x y)
  | _ -> failwith "option_map2 : None and Some at the same time"

let option_eq eq a b = match a,b with
  | None, None -> true
  | None, _ | _, None -> false
  | Some x, Some y -> eq x y

let option_map_fold f acc x = match x with
  | None -> acc, None
  | Some x -> let acc, x = f acc x in acc, Some x

(* useful iterator on int *)
let rec foldi f acc min max =
  if min > max then acc else foldi f (f acc min) (succ min) max
let rec mapi f = foldi (fun acc i -> f i::acc) []

(* useful iterator on float *)
let rec iterf f min max step =
  if min > max then () else
    (f min; iterf f (min+.step) max step)

(* useful list combinators *)

let rev_map_fold_left f acc l =
  let acc, rev =
    List.fold_left
      (fun (acc, rev) e -> let acc, e = f acc e in acc, e :: rev)
      (acc, []) l
  in
  acc, rev

let map_fold_left f acc l =
  let acc, rev = rev_map_fold_left f acc l in
  acc, List.rev rev

let list_all2 pr l1 l2 =
  try List.for_all2 pr l1 l2 with Invalid_argument _ -> false

let map_join_left map join = function
  | x :: xl -> List.fold_left (fun acc x -> join acc (map x)) (map x) xl
  | _ -> raise (Failure "map_join_left")

let list_apply f l =
  List.rev (List.fold_left (fun acc x -> List.rev_append (f x) acc) [] l)

let list_fold_product f acc l1 l2 =
  List.fold_left
    (fun acc e1 ->
       List.fold_left
         (fun acc e2 -> f acc e1 e2)
         acc l2)
    acc l1

let list_fold_product_l f acc ll =
  let ll = List.rev ll in
  let rec aux acc le = function
    | [] -> f acc le
    | l::ll -> List.fold_left (fun acc e -> aux acc (e::le) ll) acc l
  in
  aux acc [] ll

let list_compare cmp l1 l2 = match l1,l2 with
  | [], [] ->  0
  | [], _  -> -1
  | _,  [] ->  1
  | a1::l1, a2::l2 ->
      let c = cmp a1 a2 in if c = 0 then compare l1 l2 else c

let list_flatten_rev fl =
  List.fold_left (fun acc l -> List.rev_append l acc) [] fl

let list_part cmp l =
  let l = List.stable_sort cmp l in
  match l with
    | [] -> []
    | e::l ->
      let rec aux acc curr last = function
        | [] -> ((last::curr)::acc)
        | a::l when cmp last a = 0 -> aux acc (last::curr) a l
        | a::l -> aux ((last::curr)::acc) [] a l in
      aux [] [] e l

let rec list_first f = function
  | [] -> raise Not_found
  | a::l -> match f a with
      | None -> list_first f l
      | Some r -> r

let list_iteri f l =
  let rec iter i = function
    | [] -> ()
    | x :: l -> f i x; iter (i + 1) l
  in
  iter 0 l

let list_mapi f l =
  let rec map i = function
    | [] -> []
    | x :: l -> let v = f i x in v :: map (i + 1) l
  in
  map 0 l

let list_fold_lefti f acc l =
  let rec fold_left acc i = function
    | [] -> acc
    | a :: l -> fold_left (f acc i a) (i + 1) l
  in
  fold_left acc 0 l

let rec prefix n l =
  if n = 0 then []
  else if n < 0 || l = [] then invalid_arg "Util.chop"
  else List.hd l :: prefix (n - 1) (List.tl l)

let rec chop n l =
  if n = 0 then l
  else if n < 0 || l = [] then invalid_arg "Util.chop"
  else chop (n - 1) (List.tl l)

(* boolean fold accumulators *)

exception FoldSkip

let all_fn pr _ t = pr t || raise FoldSkip
let any_fn pr _ t = pr t && raise FoldSkip

(* constant boolean function *)
let ttrue _ = true
let ffalse _ = false

(* useful function on string *)
let split_string_rev s c =
  let rec aux acc i =
    try
      let j = String.index_from s i c in
      aux ((String.sub s i (j-i))::acc) (j + 1)
    with Not_found -> (String.sub s i (String.length s - i))::acc
      | Invalid_argument _ -> ""::acc in
  aux [] 0

(** usefule function on char *)
let is_uppercase c = 'A' <= c && c <= 'Z'

(* Set and Map on ints and strings *)

module Int  = struct type t = int let compare = Pervasives.compare end

module Mint = Map.Make(Int)
module Sint = Mint.Set

module Mstr = Map.Make(String)
module Sstr = Mstr.Set

(* Set, Map, Hashtbl on structures with a unique tag *)

module type Tagged =
sig
  type t
  val tag : t -> int
end

module type OrderedHash =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module OrderedHash (X : Tagged) =
struct
  type t = X.t
  let hash = X.tag
  let equal ts1 ts2 = X.tag ts1 == X.tag ts2
  let compare ts1 ts2 = Pervasives.compare (X.tag ts1) (X.tag ts2)
end

module OrderedHashList (X : Tagged) =
struct
  type t = X.t list
  let hash = Hashcons.combine_list X.tag 3
  let equ_ts ts1 ts2 = X.tag ts1 == X.tag ts2
  let equal = list_all2 equ_ts
  let cmp_ts ts1 ts2 = Pervasives.compare (X.tag ts1) (X.tag ts2)
  let compare = list_compare cmp_ts
end

module StructMake (X : Tagged) =
struct
  module T = OrderedHash(X)
  module M = Map.Make(T)
  module S = M.Set
  module H = Hashtbl.Make(T)
end

module MakeTagged (X : Hashweak.Weakey) =
struct
  type t = X.t
  let tag t = Hashweak.tag_hash (X.tag t)
end

module WeakStructMake (X : Hashweak.Weakey) =
struct
  module T = OrderedHash(MakeTagged(X))
  module M = Map.Make(T)
  module S = M.Set
  module H = Hashtbl.Make(T)
  module W = Hashweak.Make(X)
end

(* memoization *)

let memo_int size f =
  let h = Hashtbl.create size in
  fun x -> try Hashtbl.find h x
  with Not_found -> let y = f x in Hashtbl.add h x y; y

let memo_string = memo_int

