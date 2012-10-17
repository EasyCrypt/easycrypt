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

(** Useful functions *)

val ($) : ('a -> 'b) -> 'a -> 'b
val (|>) : 'a -> ('a -> 'b) -> 'b

val const : 'a -> 'b -> 'a

val const2 : 'a -> 'b -> 'c -> 'a

val const3 : 'a -> 'b -> 'c -> 'd -> 'a

val flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c

val cons : ('a -> 'b) -> 'b list -> 'a -> 'b list

(* useful option combinators *)

val of_option : 'a option -> 'a

val default_option : 'a -> 'a option -> 'a

val option_map : ('a -> 'b) -> 'a option -> 'b option

val option_iter : ('a -> unit) -> 'a option -> unit

val option_apply : 'b -> ('a -> 'b) -> 'a option -> 'b

val option_fold : ('b -> 'a -> 'b) -> 'b -> 'a option -> 'b
(** [option_fold f d o] returns [d] if [o] is [None], and
    [f d x] if [o] is [Some x] *)

val option_map2 : ('a -> 'b -> 'c) -> 'a option -> 'b option -> 'c option

val option_eq : ('a -> 'b -> bool) -> 'a option -> 'b option -> bool

val option_map_fold :
  ('a -> 'b -> 'a * 'b) -> 'a -> 'b option -> 'a * 'b option

(* useful int iterator *)
val foldi : ('a -> int -> 'a) -> 'a -> int -> int -> 'a
val mapi : (int -> 'a) -> int -> int -> 'a list

(* useful float iterator *)
val iterf : (float -> unit) -> float -> float -> float -> unit
(** [iterf f min max step] *)

(* useful list combinators *)

val rev_map_fold_left :
  ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a list -> 'acc * 'b list

val map_fold_left :
  ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a list -> 'acc * 'b list

val list_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

val map_join_left : ('a -> 'b) -> ('b -> 'b -> 'b) -> 'a list -> 'b

val list_apply : ('a -> 'b list) -> 'a list -> 'b list
(** [list_apply f [a1;..;an]] returns (f a1)@...@(f an) *)

val list_fold_product :
  ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
  (** [list_fold_product f acc l1 l2] apply the function [f] with the
      accumulator [acc] on all the pair of elements of [l1] and [l2]
      tail-reccursive *)

val list_fold_product_l :
  ('a -> 'b list -> 'a) -> 'a -> 'b list list -> 'a
  (** generalisation of {! list_fold_product}
      not tail-reccursive *)

val list_compare : ('a -> 'a -> int) -> 'a list -> 'a list -> int

val list_flatten_rev : 'a list list -> 'a list

val list_part : ('a -> 'a -> int) -> 'a list -> 'a list list
(** [list_part cmp l] returns the list of the congruence classes with
    respect to [cmp]. They are returned in reverse order *)

val list_first : ('a -> 'b option) -> 'a list -> 'b
(** [list_first f l] returns the first result of the application of
    [f] to an element of [l] which doesn't return [None]. [raise
    Not_found] if all the element of [l] return [None] *)

val list_mapi : (int -> 'a -> 'b) -> 'a list -> 'b list
val list_iteri : (int -> 'a -> unit) -> 'a list -> unit
val list_fold_lefti : ('a -> int -> 'b -> 'a) -> 'a -> 'b list -> 'a
  (** similar to List.map, List.iter and List.fold_left,
      but with element index passed as extra argument (in 0..len-1) *)

val prefix : int -> 'a list -> 'a list
  (** the first n elements of a list *)
val chop : int -> 'a list -> 'a list
  (** removes the first n elements of a list;
      raises Invalid_argument if the list is not long enough *)

(* boolean fold accumulators *)

exception FoldSkip

val all_fn : ('a -> bool) -> 'b -> 'a -> bool
(* [all_fn pr b a] return true if pr is true on a, otherwise raise FoldSkip *)
val any_fn : ('a -> bool) -> 'b -> 'a -> bool
(* [all_fn pr b a] return false if pr is false on a,
   otherwise raise FoldSkip *)

val ffalse : 'a -> bool
(** [ffalse] constant function [false] *)

val ttrue : 'a -> bool
(** [ttrue] constant function [true] *)

(* useful function on string *)
val split_string_rev : string -> char -> string list

(* useful function on char *)
val is_uppercase : char -> bool

(* Set and Map on ints and strings *)

module Mint : Map.S with type key = int
module Sint : Mint.Set

module Mstr : Map.S with type key = string
module Sstr : Mstr.Set

val memo_int : int -> (int -> 'a) -> int -> 'a
val memo_string : int -> (string -> 'a) -> string -> 'a

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

module OrderedHash (X : Tagged) : OrderedHash with type t = X.t
module OrderedHashList (X : Tagged) : OrderedHash with type t = X.t list

module StructMake (X : Tagged) :
sig
  module M : Map.S with type key = X.t
  module S : M.Set
  module H : Hashtbl.S with type key = X.t
end

module WeakStructMake (X : Hashweak.Weakey) :
sig
  module M : Map.S with type key = X.t
  module S : M.Set
  module H : Hashtbl.S with type key = X.t
  module W : Hashweak.S with type key = X.t
end

