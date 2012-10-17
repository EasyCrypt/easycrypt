(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* $Id: map.mli 10483 2010-05-31 12:48:13Z doligez $ *)

module Map : sig

(** Association tables over ordered types.

   This module implements applicative association tables, also known as
   finite maps or dictionaries, given a total ordering function
   over the keys.
   All operations over maps are purely applicative (no side-effects).
   The implementation uses balanced binary trees, and therefore searching
   and insertion take time logarithmic in the size of the map.
*)

module type OrderedType =
  sig
    type t
    (** The type of the map keys. *)

    val compare : t -> t -> int
    (** A total ordering function over the keys.
        This is a two-argument function [f] such that
        [f e1 e2] is zero if the keys [e1] and [e2] are equal,
        [f e1 e2] is strictly negative if [e1] is smaller than [e2],
        and [f e1 e2] is strictly positive if [e1] is greater than [e2].
        Example: a suitable ordering function is the generic structural
        comparison function {!Pervasives.compare}. *)
  end
(** Input signature of the functor {!Map.Make}. *)

module type S =
  sig
    type key
    (** The type of the map keys. *)

    type (+'a) t
    (** The type of maps from type [key] to type ['a]. *)

    val empty: 'a t
    (** The empty map. *)

    val is_empty: 'a t -> bool
    (** Test whether a map is empty or not. *)

    val mem: key -> 'a t -> bool
    (** [mem x m] returns [true] if [m] contains a binding for [x],
        and [false] otherwise. *)

    val add: key -> 'a -> 'a t -> 'a t
    (** [add x y m] returns a map containing the same bindings as
        [m], plus a binding of [x] to [y]. If [x] was already bound
        in [m], its previous binding disappears. *)

    val singleton: key -> 'a -> 'a t
    (** [singleton x y] returns the one-element map that contains a binding [y]
        for [x].
        @since 3.12.0 *)

    val remove: key -> 'a t -> 'a t
    (** [remove x m] returns a map containing the same bindings as
        [m], except for [x] which is unbound in the returned map. *)

    val merge:
         (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    (** [merge f m1 m2] computes a map whose keys is a subset of keys of [m1]
        and of [m2]. The presence of each such binding, and the corresponding
        value, is determined with the function [f].
        @since 3.12.0 *)

    val compare: ('a -> 'a -> int) -> 'a t -> 'a t -> int
    (** Total ordering between maps.  The first argument is a total ordering
        used to compare data associated with equal keys in the two maps. *)

    val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    (** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are
        equal, that is, contain equal keys and associate them with
        equal data.  [cmp] is the equality predicate used to compare
        the data associated with the keys. *)

    val iter: (key -> 'a -> unit) -> 'a t -> unit
    (** [iter f m] applies [f] to all bindings in map [m].
       [f] receives the key as first argument, and the associated value
       as second argument.  The bindings are passed to [f] in increasing
       order with respect to the ordering over the type of the keys. *)

    val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    (** [fold f m a] computes [(f kN dN ... (f k1 d1 a)...)], where
        [k1 ... kN] are the keys of all bindings in [m] (in increasing
        order), and [d1 ... dN] are the associated data. *)

    val for_all: (key -> 'a -> bool) -> 'a t -> bool
    (** [for_all p m] checks if all the bindings of the map
        satisfy the predicate [p].
        @since 3.12.0 *)

    val exists: (key -> 'a -> bool) -> 'a t -> bool
    (** [exists p m] checks if at least one binding of the map
        satisfy the predicate [p].
        @since 3.12.0 *)

    val filter: (key -> 'a -> bool) -> 'a t -> 'a t
    (** [filter p m] returns the map with all the bindings in [m]
        that satisfy predicate [p].
        @since 3.12.0 *)

    val partition: (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    (** [partition p m] returns a pair of maps [(m1, m2)], where
        [m1] contains all the bindings of [s] that satisfy the
        predicate [p], and [m2] is the map with all the bindings of
        [s] that do not satisfy [p].
        @since 3.12.0 *)

    val cardinal: 'a t -> int
    (** Return the number of bindings of a map.
        @since 3.12.0 *)

    val bindings: 'a t -> (key * 'a) list
    (** Return the list of all bindings of the given map.
        The returned list is sorted in increasing order with respect
        to the ordering [Ord.compare], where [Ord] is the argument
        given to {!Map.Make}.
        @since 3.12.0 *)

    val min_binding: 'a t -> (key * 'a)
    (** Return the smallest binding of the given map
        (with respect to the [Ord.compare] ordering), or raise
        [Not_found] if the map is empty.
        @since 3.12.0 *)

    val max_binding: 'a t -> (key * 'a)
    (** Same as {!Map.S.max_binding}, but returns the largest
        binding of the given map.
        @since 3.12.0 *)

    val choose: 'a t -> (key * 'a)
    (** Return one binding of the given map, or raise [Not_found] if
        the map is empty. Which binding is chosen is unspecified,
        but equal bindings will be chosen for equal maps.
        @since 3.12.0 *)

    val split: key -> 'a t -> 'a t * 'a option * 'a t
    (** [split x m] returns a triple [(l, data, r)], where
          [l] is the map with all the bindings of [m] whose key
        is strictly less than [x];
          [r] is the map with all the bindings of [m] whose key
        is strictly greater than [x];
          [data] is [None] if [m] contains no binding for [x],
          or [Some v] if [m] binds [v] to [x].
        @since 3.12.0 *)

    val find: key -> 'a t -> 'a
    (** [find x m] returns the current binding of [x] in [m],
        or raises [Not_found] if no such binding exists. *)

    val map: ('a -> 'b) -> 'a t -> 'b t
    (** [map f m] returns a map with same domain as [m], where
        the associated value [a] of all bindings of [m] has been
        replaced by the result of the application of [f] to [a].
        The bindings are passed to [f] in increasing order
        with respect to the ordering over the type of the keys. *)

    val mapi: (key -> 'a -> 'b) -> 'a t -> 'b t
    (** Same as {!Map.S.map}, but the function receives as arguments both
        the key and the associated value for each binding of the map. *)


    (** {3} Added into why stdlib version *)

    val change : key -> ('a option -> 'a option) -> 'a t -> 'a t
    (** [change x f m] returns a map containing the same bindings as
        [m], except the binding of [x] in [m] is changed from [y] to
        [f (Some y)] if [m] contains a binding of [x], otherwise the
        binding of [x] becomes [f None].

        [change x f m] corresponds to a more efficient way to do
        [add x (try f (Some (find x m)) with Not_found -> f None) m] *)

    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    (** [union f m1 m2] computes a map whose keys is a subset of keys
        of [m1] and of [m2]. If a binding is present in [m1] (resp. [m2])
        and not in [m2] (resp. [m1]) the same binding is present in
        the result. The function [f] is called only in ambiguous cases. *)

    val inter : (key -> 'a -> 'b -> 'c option) -> 'a t -> 'b t -> 'c t
    (** [inter f m1 m2] computes a map whose keys is a subset of
        the intersection of keys of [m1] and of [m2]. *)

    val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t
    (** [diff f m1 m2] computes a map whose keys is a subset of keys
        of [m1]. [f] is applied on key which belongs to [m1] and [m2]
        if [f] returns [None] the binding is removed from [m1],
        otherwise [Some d1] is returned, the key binds to [d1] in [m1] *)

    val submap : (key -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool
    (** [submap pr m1 m2] verifies that all the keys in m1 are in m2
        and that for each such binding pr is verified. *)

    val disjoint : (key -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool
    (** [disjoint pr m1 m2] verifies that for every common key in m1
        and m2, pr is verified. *)

    val set_inter : 'a t -> 'b t -> 'a t
    (** [set_inter = inter (fun _ x _ -> Some x)] *)

    val set_diff : 'a t -> 'b t -> 'a t
    (** [set_diff = diff (fun _ _ _ -> None)] *)

    val set_submap : 'a t -> 'b t -> bool
    (** [set_submap = submap (fun _ _ _ -> true)] *)

    val set_disjoint : 'a t -> 'b t -> bool
    (** [set_disjoint = disjoint (fun _ _ _ -> false)] *)

    val find_default : key -> 'a -> 'a t -> 'a
    (** [find_default x d m] returns the current binding of [x] in [m],
        or return [d] if no such binding exists. *)

    val find_option : key -> 'a t -> 'a option
    (** [find_default x d m] returns the [Some] of the current binding
        of [x] in [m], or return [None] if no such binding exists. *)

    val map_filter: ('a -> 'b option) -> 'a t -> 'b t
    (** Same as {!Map.S.map}, but may remove bindings. *)

    val mapi_filter: (key -> 'a -> 'b option) -> 'a t -> 'b t
    (** Same as {!Map.S.mapi}, but may remove bindings. *)

    val mapi_fold:
      (key -> 'a -> 'acc -> 'acc * 'b) -> 'a t -> 'acc -> 'acc * 'b t
    (** fold and map at the same time *)

    val fold2_inter: (key -> 'a -> 'b -> 'c -> 'c) -> 'a t -> 'b t -> 'c -> 'c
    (** fold the common keys of two map at the same time *)

    val fold2_union: (key -> 'a option -> 'b option -> 'c -> 'c)
      -> 'a t -> 'b t -> 'c -> 'c
    (** fold the keys which appear in one of the two map at the same time  *)

    val translate : (key -> key) -> 'a t -> 'a t
    (** [translate f m] translates the keys in the map [m] by the
        function [f]. [f] must be strictly monotone on the key of [m].
        Otherwise it raises invalid_arg *)

    val mapi_filter_fold:
      (key -> 'a -> 'acc -> 'acc * 'b option) -> 'a t -> 'acc -> 'acc * 'b t
    (** Same as {!Map.S.mapi_fold}, but may remove bindings. *)


    val add_new : key -> 'a -> exn -> 'a t -> 'a t
    (** [add_new x v e m] binds [x] to [v] in [m] if [x] is not bound,
        and raises [exn] otherwise. *)

    val keys: 'a t -> key list
    (** Return the list of all keys of the given map.
        The returned list is sorted in increasing order with respect
        to the ordering [Ord.compare], where [Ord] is the argument
        given to {!Map.Make}. *)

    val values: 'a t -> 'a list
    (** Return the list of all values of the given map.
        The returned list is sorted in increasing order with respect
        to the ordering [Ord.compare] of the keys, where [Ord] is the argument
        given to {!Map.Make}. *)

    module type Set =
    sig
      type elt = key
      type set = unit t
      type t = set
      (** The type of sets of type [elt]. *)

      val empty: t
      (** The empty set. *)

      val is_empty: t -> bool
      (** Test whether a set is empty or not. *)

      val mem: elt -> t -> bool
      (** [mem x s] returns [true] if [s] contains [x],
          and [false] otherwise. *)

      val add: elt -> t -> t
      (** [add x s] returns a set containing the same elements as
          [s], plus [x]. *)

      val singleton: elt -> t
      (** [singleton x] returns the one-element set that contains [x]. *)

      val remove: elt -> t -> t
      (** [remove x s] returns a set containing the same elements as [s],
          except for [x]. *)

      val merge: (elt -> bool -> bool -> bool) -> t -> t -> t
      (** [merge f s1 s2] computes a set whose elts is a subset of elts
          of [s1] and of [s2]. The presence of each such element is
          determined with the function [f]. *)

      val compare: t -> t -> int
      (** Total ordering between sets. *)

      val equal: t -> t -> bool
      (** [equal s1 s2] tests whether the sets [s1] and [s2] are equal. *)

      val subset: t -> t -> bool
      (** [subset s1 s2] tests whether the set [s1] is a subset of [s2]. *)

      val disjoint: t -> t -> bool
      (** [disjoint s1 s2] tests whether the sets [s1] and [s2]
          are disjoint. *)

      val iter: (elt -> unit) -> t -> unit
      (** [iter f s] applies [f] to all elements of [s].
          The elements are passed to [f] in increasing order with respect
          to the ordering over the type of the elts. *)

      val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
      (** [fold f s a] computes [(f eN ... (f e1 a)...)],
          where [e1 ... eN] are the element of [s] in increasing order. *)

      val for_all: (elt -> bool) -> t -> bool
      (** [for_all p s] checks if all the elements of [s] satisfy
          the predicate [p]. *)

      val exists: (elt -> bool) -> t -> bool
      (** [exists p s] checks if at least one element of [s] satisfies
          the predicate [p]. *)

      val filter: (elt -> bool) -> t -> t
      (** [filter p s] returns the set with all the elements of [s]
          that satisfy predicate [p]. *)

      val partition: (elt -> bool) -> t -> t * t
      (** [partition p s] returns a pair of sets [(s1, s2)], where
          [s1] contains all the elements of [s] that satisfy the
          predicate [p], and [s2] is the map with all the elements
          of [s] that do not satisfy [p]. *)

      val cardinal: t -> int
      (** Return the number of elements in a set. *)

      val elements: t -> elt list
      (** Return the list of all elements of the given set.
          The returned list is sorted in increasing order. *)

      val min_elt: t -> elt
      (** Return the smallest element of the given set or raise
          [Not_found] if the set is empty. *)

      val max_elt: t -> elt
      (** Return the largest element of the given set or raise
          [Not_found] if the set is empty. *)

      val choose: t -> elt
      (** Return one element of the given set, or raise [Not_found] if
          the set is empty. Which element is chosen is unspecified,
          but equal elements will be chosen for equal sets. *)

      val split: elt -> t -> t * bool * t
      (** [split x s] returns a triple [(l, mem, r)], where
          [l] is the set with all the elements of [s] that are
          strictly less than [x];
          [r] is the set with all the elements of [s] that are
          strictly greater than [x];
          [mem] is [true] if [x] belongs to [s] and [false] otherwise. *)

      val change : elt -> (bool -> bool) -> t -> t
      (** [change x f s] returns a set containing the same elements as
          [s], except [x] which is added to [s] if [f (mem x s)] returns
          [true] and removed otherwise. *)

      val union : t -> t -> t
      (** [union f s1 s2] computes the union of two sets *)

      val inter : t -> t -> t
      (** [inter f s1 s2] computes the intersection of two sets *)

      val diff : t -> t -> t
      (** [diss f s1 s2] computes the difference of two sets *)

      val fold2:  (elt -> 'a -> 'a) -> t -> t -> 'a -> 'a
      (** [fold f s1 s2 a] computes [(f eN ... (f e1 a)...)],
          where [e1 ... eN] are the element of [s1] and [s2]
          in increasing order. *)

      val translate : (elt -> elt) -> t -> t
      (** [translate f s] translates the elements in the set [s] by the
          function [f]. [f] must be strictly monotone on the elements of [s].
          Otherwise it raises invalid_arg *)

      val add_new : elt -> exn -> t -> t
      (** [add_new x e s] adds [x] to [s] if [s] does not contain [x],
          and raises [exn] otherwise. *)
    end

    module Set : Set

  end

(** Output signature of the functor {!Map.Make}. *)

module Make (Ord : OrderedType) : S with type key = Ord.t
(** Functor building an implementation of the map/set structure
    given a totally ordered type. *)

end
