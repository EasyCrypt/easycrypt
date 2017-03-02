(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require export ExtEq Fun.

(* -------------------------------------------------------------------- *)
lemma pred_ext (P Q : 'a -> bool):
  P = Q <=> forall x, P x <=> Q x.
proof. by split=> //= h; apply/fun_ext=> x; rewrite h. qed.

(*** Working with predicates *)
(** Lifting boolean operators to predicates *)
op pred0  ['a] = fun (x : 'a) => false.
op predT  ['a] = fun (x : 'a) => true.
op predI  ['a] = fun (p1 p2 : 'a -> bool) x => p1 x /\ p2 x.
op predU  ['a] = fun (p1 p2 : 'a -> bool) x => p1 x \/ p2 x.
op predC  ['a] = fun (p : 'a -> bool) x => ! (p x).
op predD  ['a] = fun (p1 p2 : 'a -> bool) x => !p2 x /\ p1 x.

op pred1  ['a] = fun (c x : 'a) => x = c.
op predU1 ['a] = fun (c : 'a) (p : 'a -> bool) (x : 'a) => x = c \/ p x.
op predC1 ['a] = fun (c : 'a) (x : 'a) => x <> c.
op predD1 ['a] = fun (p : 'a -> bool) (c : 'a) (x : 'a) => x <> c /\ p x.

(** Subpredicate *)
pred (<=) (p q:'a -> bool) = (* subpred *)
  forall a, p a => q a.

pred (< ) (p q:'a -> bool) = (* proper *)
  p <= q /\ !(q <= p).

(* Lemmas on inclusion *)
lemma nosmt subpred_eqP (p1 p2 : 'a -> bool):
  (forall x, p1 x <=> p2 x) <=> (p1 <= p2 /\ p2 <= p1)
by [].

lemma nosmt subpred_refl (X : 'a -> bool): X <= X
by [].

lemma nosmt subpred_asym (X Y:'a -> bool):
  X <= Y => Y <= X => X = Y
by (rewrite fun_ext; smt).

lemma nosmt subpred_trans (X Y Z:'a -> bool):
  X <= Y => Y <= Z => X <= Z
by [].

(** Lemmas **)
lemma pred1E (c : 'a) : pred1 c = ((=) c).
proof. by apply fun_ext=> x; rewrite (eq_sym c). qed.

lemma predU1l (x y : 'a) b : x = y => (x = y) \/ b
by [].

lemma predU1r (x y : 'a) b : b => (x = y) \/ b
by [].

lemma eqVneq (x y : 'a) : x = y \/ x <> y
by [].

lemma predT_comp ['a 'b] (p : 'a -> 'b) : predT \o p = predT.
proof. by []. qed.

lemma predIC (p1 p2 : 'a -> bool) : predI p1 p2 = predI p2 p1.
proof. by apply fun_ext=> x; rewrite /predI andC. qed.

lemma predCpredI (p : 'a -> bool) : predI (predC p) p = pred0.
proof. by apply/fun_ext=> x /=; case (p x); delta=> ->. qed. (* delta *)

lemma predCpredU (p : 'a -> bool) : predU (predC p) p = predT.
proof. by apply fun_ext=> x /=; case (p x); delta=> ->. qed. (* delta *)

lemma nosmt subpredUl (p1 p2 : 'a -> bool):
  p1 <= predU p1 p2
by [].

lemma nosmt subpredUr (p1 p2 : 'a -> bool):
  p2 <= predU p1 p2
by [].

lemma nosmt predIsubpredl (p1 p2 : 'a -> bool):
  predI p1 p2 <= p1
by [].

lemma nosmt predIsubpredr (p1 p2 : 'a -> bool):
  predI p1 p2 <= p2
by [].

lemma nosmt predTofV (f : 'a -> 'b): predT \o f = predT.
proof. by apply/fun_ext=> x. qed.
