(* Copyright Jeremy Yallop 2007.
   Copyright Grégoire Henry 2011.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

type ('a, 'b) either = Left of 'a | Right of 'b

val either_partition :
  ('a -> ('b, 'c) either) -> 'a list -> 'b list * 'c list

module List : sig
  include module type of List
  val fold_left1 : ('a -> 'a -> 'a) -> 'a list -> 'a
  val fold_right1 : ('a -> 'a -> 'a) -> 'a list -> 'a
  val range : int -> int -> int list
  val last : 'a list -> 'a
  val concat_map : ('a -> 'b list) -> 'a list -> 'b list
  val concat_map2 : ('a -> 'b -> 'c list) -> 'a list -> 'b list -> 'c list
  val mapn : ?init:int -> ('a -> int -> 'b) -> 'a list -> 'b list
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
end

module F : sig
  val id : 'a -> 'a
  val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
end

module Option : sig
  val map : ('a -> 'b) -> 'a option -> 'b option
end

module DumpAst : sig
  val ident : Camlp4.PreCast.Ast.ident -> string
  val ctyp : Camlp4.PreCast.Ast.ctyp -> string
end

module Map : sig

  module type OrderedType = Map.OrderedType

  module type S = sig
    include Map.S
    exception Not_found of key
    val fromList : (key * 'a) list -> 'a t
    val union_disjoint : 'a t list -> 'a t
    val union_disjoint2 : 'a t -> 'a t -> 'a t
  end

  module Make (Ord : OrderedType) : S with type key = Ord.t

end

module Set : sig

  module type OrderedType = Set.OrderedType

  module type S = sig
    include Set.S
    val toList : t -> elt list
    val fromList : elt list -> t
  end

  module Make (Ord : OrderedType) : S with type elt = Ord.t

end

val random_id : int -> string

val tag_hash : string -> int

val typevar_of_int : int -> string
