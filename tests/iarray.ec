require import AllCore.
require import IArray.

(* Symbolic n: the equational surface is usable by rewriting. *)
lemma sym_get_set {n} ['a] (a : 'a array<:n>) (i : int) (x : 'a) :
  0 <= i < n => a.[i <- x].[i] = x.
proof. by move=> hi; rewrite get_set. qed.

lemma sym_set_set {n} ['a] (a : 'a array<:n>) (i j : int) (x y : 'a) :
  i <> j => a.[i <- x].[j <- y] = a.[j <- y].[i <- x].
proof. by move=> ne; rewrite set_set_swap. qed.

lemma sym_map_get {n} ['a 'b] (f : 'a -> 'b) (a : 'a array<:n>) (i : int) :
  0 <= i < n => (map f a).[i] = f a.[i].
proof. by move=> hi; rewrite mapE. qed.

(* Concrete index: same lemmas specialise. *)
lemma cn_get_set ['a] (a : 'a array<:8>) (x : 'a) :
  a.[3 <- x].[3] = x.
proof. by rewrite get_set. qed.
