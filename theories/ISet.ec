(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

require import Int.
require import Pred.

(** This is a library for (possibly infinite) sets,
    usable as domains for maps, but not really in
    computations. *)
(* Ideally, a lot of the lemmas could be inherited from general
   algebraic theories (ring, partial order...) *)
type 'a set.

(** We use membership as core specification *)
op mem:'a -> 'a set -> bool.

(** Equality *)
pred (==) (X1 X2:'a set) = forall x, mem x X1 <=> mem x X2.

(* Extension is an equivalence relation *)
lemma nosmt eq_refl (X:'a set): X == X by [].
lemma nosmt eq_symm (X Y:'a set): X == Y => Y == X by [].
lemma nosmt eq_tran (X Y Z:'a set): X == Y => Y == Z => X == Z by [].

(* And we can use it as equality *)
axiom set_ext (X1 X2:'a set): X1 == X2 => X1 = X2.

(** Inclusion *)
pred (<=) (X1 X2:'a set) = forall x, mem x X1 => mem x X2.

(* Inclusion is a partial order *)
lemma leq_refl (X:'a set):
  X <= X
by trivial.

lemma leq_asym (X Y:'a set):
  X <= Y => Y <= X => X = Y
by (intros=> X_leq_Y Y_leq_X; apply set_ext; smt).

lemma leq_tran (X Y Z:'a set):
  X <= Y => Y <= Z => X <= Z.
proof strict.
by rewrite /Self.(<=); intros=> X_leq_Y Y_leq_Z x x_in_X;
   apply Y_leq_Z=> //; apply X_leq_Y=> //.
qed.

pred (>=) (X1 X2:'a set) = X2 <= X1.
pred (<)  (X1 X2:'a set) = X1 <= X2 /\ X1 <> X2.
pred (>)  (X1 X2:'a set) = X2 < X1.

(** mem *)
op empty:'a set.
axiom mem_empty (x:'a): !(mem x empty).

lemma empty_leq (X:'a set): empty <= X by [].
lemma empty_unique (X:'a set):
  (forall (x:'a), !(mem x X)) <=> X = empty
by [].

(** add *)
op add:'a -> 'a set -> 'a set.
axiom mem_add (x y:'a) X:
  (mem x (add y X)) = (mem x X \/ x = y).

lemma add_in_id (x:'a) X:
  mem x X => X = add x X
by (intros=> x_in_X; apply set_ext; smt).

lemma leq_add (x:'a) X: X <= add x X by [].

(** rm *)
op rm:'a -> 'a set -> 'a set.
axiom mem_rm_eq (x:'a) X:
  !(mem x (rm x X)).
axiom mem_rm_neq (x x':'a) X:
  x <> x' => mem x (rm x' X) = mem x X.

lemma mem_rm (x x':'a) (X:'a set):
  mem x (rm x' X) = (mem x X /\ x <> x').
proof strict.
case (x = x')=> x_x'.
  by subst x'; logic; rewrite neqF; apply mem_rm_eq.
  by logic; apply mem_rm_neq.
qed.

lemma rm_add_eq (x:'a) X:
  rm x (add x X) = rm x X
by (apply set_ext; smt).

lemma rm_add_neq (x x':'a) X:
  x <> x' => rm x (add x' X) = add x' (rm x X).
proof strict.
intros=> x_x'; apply set_ext;
delta (==); beta=> x0;
case (x = x0)=> x_x0.
  by subst x0; smt.
  by rewrite mem_rm_neq; smt.
qed.

lemma add_rm_in (x:'a) X:
  mem x X => add x (rm x X) = X
by (intros=> x_in_X; apply set_ext; smt).

lemma add_destruct (x:'a) X:
  (exists X', !mem x X' /\ X = add x X') <=> mem x X
by [].

(** single *)
op single:'a -> 'a set.
axiom mem_single_eq (x:'a):
  mem x (single x).
axiom mem_single_neq (x x':'a):
  x <> x' => !mem x (single x').

(** compl *)
op compl:'a set -> 'a set.
axiom mem_compl x (X:'a set):
  mem x (compl X) <=> !mem x X.

lemma complK (X:'a set):
  compl (compl X) = X
by (apply set_ext; smt).

(** univ *)
const univ:'a set = compl empty.
lemma mem_univ (x:'a):
  mem x univ
by [].

(** union *)
op union:'a set -> 'a set -> 'a set.
axiom mem_union x (X1 X2:'a set):
  mem x (union X1 X2) <=> (mem x X1 \/ mem x X2).

lemma unionC (X1 X2:'a set):
  union X1 X2 = union X2 X1
by (apply set_ext; smt).

lemma unionA (X1 X2 X3:'a set):
  union (union X1 X2) X3 = union X1 (union X2 X3)
by (apply set_ext; smt).

lemma union0s (X:'a set):
  union empty X = X
by (apply set_ext; smt).

lemma unionLs (X1 X2:'a set):
  X1 <= union X1 X2
by [].

lemma unionK (X:'a set):
  union X X = X
by (apply set_ext; smt).

lemma unionNs (X:'a set):
  union X (compl X) = univ
by (apply set_ext; smt).

lemma union1s (X:'a set):
  union univ X = univ
by (apply set_ext; smt).

(** inter *)
op inter:'a set -> 'a set -> 'a set.
axiom mem_inter x (X1 X2:'a set):
  mem x (inter X1 X2) <=> (mem x X1 /\ mem x X2).

lemma interC (X1 X2:'a set):
  inter X1 X2 = inter X2 X1
by (apply set_ext; smt).

lemma interA (X1 X2 X3:'a set):
  inter (inter X1 X2) X3 = inter X1 (inter X2 X3)
by (apply set_ext; smt).

lemma interGs (X1 X2:'a set):
  inter X1 X2 <= X1
by [].

lemma interK (X:'a set):
  inter X X = X
by (apply set_ext; smt).

lemma inter0s (X:'a set):
  inter empty X = empty
by (apply set_ext; smt).

lemma inter1s (X:'a set):
  inter X univ = X
by (apply set_ext; smt).

(** all *)
op all:('a -> bool) -> 'a set -> bool.
axiom all_def (p:('a -> bool)) X:
  all p X <=> (forall x, mem x X => p x).

(** any *)
op any:('a -> bool) -> 'a set -> bool.
axiom any_def (p:('a -> bool)) X:
  any p X <=> (exists x, mem x X /\ p x).

(** filter *)
op filter:('a -> bool) -> 'a set -> 'a set.
axiom mem_filter x (p:('a -> bool)) X:
  mem x (filter p X) <=> (mem x X /\ p x).

lemma filter_cpTrue (X:'a set):
  filter predT X = X
by (apply set_ext; smt).

lemma filter_cpEq_in (x:'a) X:
  mem x X => filter ((=) x) X = single x
by (intros=> x_in_X; apply set_ext; smt).

lemma leq_filter (p:('a -> bool)) X:
  filter p X <= X
by [].

lemma filter_empty (p:'a -> bool):
  filter p empty = empty.
proof strict.
by apply set_ext=> x;
   rewrite mem_filter -(nnot (mem x empty)) mem_empty.
qed.

lemma rm_filter x (p:'a -> bool) s:
  rm x (filter p s) = filter p (rm x s).
proof strict.
by apply set_ext=> a;
   rewrite mem_filter mem_rm mem_filter mem_rm.
qed.

(** create *)
op create: ('a -> bool) -> 'a set.

axiom mem_create (x:'a) p:
  mem x (create p) <=> p x.

lemma create_def (p:('a -> bool)):
  create p = filter p univ.
proof strict.
by apply set_ext=> x;
   rewrite mem_filter mem_univ /= mem_create.
qed.

(*** Cross-operator lemmas *)
(** This is another scary one *)
lemma inter_filter (X Y:'a set):
  inter X Y = filter (fun x, mem x X) Y.
proof strict.
by apply set_ext=> x; rewrite mem_inter mem_filter.
qed.

(*** Finite sets and isomorphism between finite ISets and FSet *)
theory Finite.
  require        FSet.

  pred (==) (X:'a set) (Y:'a FSet.set) =
    forall (x:'a), mem x X <=> FSet.mem x Y.

  pred finite (X:'a set) =
    exists (X':'a FSet.set), X == X'.

  op toFSet: 'a set -> 'a FSet.set.
  axiom toFSet_cor (X:'a set):
    finite X => X == toFSet X.

  op fromFSet: 'a FSet.set -> 'a set.
  axiom fromFSet_cor (X:'a FSet.set):
    fromFSet X == X.

  lemma mem_toFSet (x:'a) X: finite X =>
    FSet.mem x (toFSet X) <=> mem x X.
  proof strict.
  intros=> fX; rewrite -eq_iff eq_sym eq_iff.
  generalize x; rewrite -/(Finite.(==) X _).
  by apply toFSet_cor.
  qed.

  lemma finite_fromFSet (X:'a FSet.set):
    finite (fromFSet X)
  by (exists X; apply fromFSet_cor).

  lemma toFSetI (X Y:'a set):
    finite X => finite Y =>
    toFSet X = toFSet Y => X = Y.
  proof strict.
  by intros=> fX fY eq_toFSet; apply set_ext=> x;
     rewrite 2?toFSet_cor ?eq_toFSet.
  qed.

  lemma fromFSetI (X Y:'a FSet.set):
    fromFSet X = fromFSet Y => X = Y.
  proof strict.
  by intros=> eq_fromFSet; apply FSet.set_ext=> x;
     rewrite -2!fromFSet_cor eq_fromFSet.
  qed.

  lemma toFSet_fromFSet (X:'a FSet.set):
    toFSet (fromFSet X) = X.
  proof strict.
  by apply FSet.set_ext=> x;
     rewrite -toFSet_cor ?fromFSet_cor ?finite_fromFSet.
  qed.

  lemma fromFSet_toFSet (X:'a set):
    finite X =>
    fromFSet (toFSet X) = X.
  proof strict.
  by intros=> fX; apply set_ext=> x; rewrite fromFSet_cor toFSet_cor.
  qed.

  (* We should then show that all set operations correspond as expected *)
  lemma finite_empty: finite empty<:'a>.
  proof strict.
  exists FSet.empty=> x.
  rewrite (_: (mem x empty) = false) 1:neqF 1:mem_empty //.
  by rewrite (_: (FSet.mem x (FSet.empty)) = false) 1:neqF 1:FSet.mem_empty.
  qed.

  lemma toFSet_empty: toFSet empty<:'a> = FSet.empty.
  proof strict.
  by apply FSet.set_ext; smt.
  qed.

  lemma finite_add (X :'a set) x:
    finite X => finite (add x X).
  proof strict.
  intros=> [Y X_Y].
  exists (FSet.add x Y)=> y.
  by rewrite FSet.mem_add mem_add  X_Y.
  qed.

  lemma addM (X :'a set) x:
    finite X => toFSet (add x X) = FSet.add x (toFSet X).
  proof strict.
  intros=> fX; apply FSet.set_ext=> y.
  rewrite (mem_toFSet y (add x X)) ?finite_add //.
  by rewrite FSet.mem_add mem_add (mem_toFSet y X).
  qed.

  lemma finite_filter p (X:'a set):
    finite X =>
    finite (filter p X).
  proof strict.
  intros=> [X' X_X'].
  exists (FSet.filter p X')=> x.
  by rewrite mem_filter FSet.mem_filter X_X'.
  qed.

  lemma filterM p (X:'a set):
    finite X =>
    toFSet (filter p X) = FSet.filter p (toFSet X).
  proof strict.
  intros=> fX; apply FSet.set_ext=> x.
  rewrite mem_toFSet ?finite_filter //.
  by rewrite mem_filter FSet.mem_filter mem_toFSet.
  qed.

  lemma finite_union (X Y:'a set):
    finite X =>
    finite Y =>
    finite (union X Y).
  proof strict.
  intros=> [X' X_X'] [Y' Y_Y'].
  exists (FSet.union X' Y')=> x.
  by rewrite mem_union FSet.mem_union X_X' Y_Y'.
  qed.

  lemma finite_prod:
     finite univ<:'a> =>
     finite univ<:'b> =>
     finite univ<:'a * 'b>.
  proof strict.
  case=> [A eqA] [B eqB].
  exists (FSet.Product.(**) A B)=> x; rewrite mem_univ.
  by rewrite -FSet.Product.mem_prod -eqA -eqB !mem_univ.
  qed.

  lemma unionM (X Y:'a set):
    finite X =>
    finite Y =>
    toFSet (union X Y) = FSet.union (toFSet X) (toFSet Y).
  proof strict.
  intros=> fX fY; apply FSet.set_ext=> x.
  rewrite mem_toFSet ?finite_union //.
  by rewrite FSet.mem_union mem_union !mem_toFSet.
  qed.

  lemma finite_inter (X Y:'a set):
    finite Y =>
    finite (inter X Y).
  proof strict.
  intros=> fY.
  by rewrite inter_filter finite_filter.
  qed.

  lemma interM (X Y:'a set):
    finite X =>
    finite Y =>
    toFSet (inter X Y) = FSet.inter (toFSet X) (toFSet Y).
  proof strict.
  intros=> fX fY; apply FSet.set_ext=> x.
  rewrite mem_toFSet ?finite_inter //.
  by rewrite mem_inter FSet.mem_inter !mem_toFSet.
  qed.
end Finite.
