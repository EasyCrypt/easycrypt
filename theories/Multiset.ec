(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

require import Logic.
require import Int.

(* Core Datatype *)
type 'a multiset.

op empty: 'a multiset.
op   add  : 'a multiset -> 'a -> 'a multiset.

axiom induction: forall (xs:'a multiset) (p:'a multiset -> bool),
  p empty =>
  (forall xs x, p xs => p (add xs x)) =>
  p xs.

(* count *)
op count: 'a multiset -> ('a -> bool) -> int.

axiom count_empty: forall (p:'a -> bool),
  count empty p = 0.

axiom count_nonempty: forall (x:'a) xs (p:'a -> bool),
  count (add xs x) p = count xs p + ((p x) ? 1 : 0).

(* Extentional Equality *)
op eq(x y:'a):bool = x = y.

pred (==)(m0, m1:'a multiset) = forall (x:'a),
  count m0 (eq x) = count m1 (eq x).

axiom extensionality: forall (m0 m1:'a multiset),
  m0 == m1 => m0 = m1.

(* del *)
op del: 'a multiset -> 'a -> 'a multiset.

axiom del_empty: forall (x:'a),
  del empty x = empty.

axiom del_nonempty: forall (x y:'a) xs,
  del (add xs x) y = (x = y) ? xs : add (del xs y) x.

(* lemmas *)
lemma count_pos: forall (xs:'a multiset) p,
  0 <= count xs p.
proof -strict.
intros xs p.
apply (induction<:'a> xs (fun xs, 0 <= count xs p) _ _);
smt.
qed.

lemma card_add: forall (x:'a) xs,
  count (add xs x) (fun x, true) = 1 + count xs (fun x, true).
proof -strict. by intros x xs; smt. qed.

lemma add_commutative: forall (x y:'a) xs,
  add (add xs x) y = add (add xs y) x.
proof -strict.
intros x y xs;
apply (extensionality<:'a> (add (add xs x) y) (add (add xs y) x) _);
smt.
qed.
