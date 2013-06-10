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
proof.
intros xs p.
apply (induction<:'a> xs (lambda xs, 0 <= count xs p) _ _);
trivial.
save.

lemma card_add: forall (x:'a) xs,
  count (add xs x) (lambda x, true) = 1 + count xs (lambda x, true).
proof.
intros x xs; generalize x; clear x.
apply (induction<:'a> xs 
 (lambda xs, forall x, 
  count (add xs x) (lambda x, true) = 1 + count xs (lambda x, true)) _ _).
trivial.
simplify; intros xs1 x H x1.
rewrite (count_nonempty<:'a> x xs1 (lambda x, true)).
rewrite (count_nonempty<:'a> x1 (add xs1 x) (lambda x, true)).
rewrite (H x); simplify.
generalize (count xs1 (lambda (x : 'a), true)).
trivial.
save.

lemma add_commutative: forall (x y:'a) xs,
  add (add xs x) y = add (add xs y) x.
proof.
intros x y xs;
apply (extensionality<:'a> (add (add xs x) y) (add (add xs y) x) _);
trivial.
save.
