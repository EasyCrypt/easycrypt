require import Int.
require import Fun.

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
lemma nosmt eq_refl: forall (X:'a set), X == X by [].
lemma nosmt eq_symm: forall (X Y:'a set), X == Y => Y == X by [].
lemma nosmt eq_tran: forall (X Y Z:'a set), X == Y => Y == Z => X == Z by [].

(* And we can use it as equality *)
axiom set_ext: forall (X1 X2:'a set), X1 == X2 => X1 = X2.

(** Inclusion *)
pred (<=) (X1 X2:'a set) = forall x, mem x X1 => mem x X2.

(* Inclusion is a partial order *)
lemma leq_refl: forall (X:'a set),
  X <= X
by trivial.

lemma leq_asym: forall (X Y:'a set),
  X <= Y => Y <= X => X = Y
by (intros=> X Y X_leq_Y Y_leq_X; apply set_ext; smt).

lemma leq_tran: forall (X Y Z:'a set),
  X <= Y => Y <= Z => X <= Z.
proof strict.
by delta (<=) beta; intros=> X Y Z X_leq_Y Y_leq_Z x x_in_X;
   apply Y_leq_Z=> //; apply X_leq_Y=> //.
qed.

pred (>=) (X1 X2:'a set) = X2 <= X1.
pred (<) (X1 X2:'a set) = X1 <= X2 /\ X1 <> X2.
pred (>) (X1 X2:'a set) = X2 < X1.

(** mem *)
op empty:'a set.
axiom mem_empty: forall (x:'a), !(mem x empty).

lemma empty_leq: forall (X:'a set), empty <= X by [].
lemma empty_unique: forall (X:'a set),
  (forall (x:'a), !(mem x X)) <=> X = empty
by [].

(** add *)
op add:'a -> 'a set -> 'a set.
axiom mem_add: forall (x y:'a) X,
  (mem x (add y X)) = (mem x X \/ x = y).

lemma add_in_id: forall (x:'a) X,
  mem x X => X = add x X
by (intros=> x X x_in_X; apply set_ext; smt).

lemma leq_add: forall (x:'a) X, X <= add x X by [].

(** rm *)
op rm:'a -> 'a set -> 'a set.
axiom mem_rm_eq: forall (x:'a) X,
  !(mem x (rm x X)).
axiom mem_rm_neq: forall (x x':'a) X,
  x <> x' => mem x (rm x' X) = mem x X.

lemma rm_add_eq: forall (x:'a) X,
  rm x (add x X) = rm x X
by (intros=> x X; apply set_ext; smt).

lemma rm_add_neq: forall (x x':'a) X,
  x <> x' => rm x (add x' X) = add x' (rm x X).
proof strict.
intros=> x x' X x_x'; apply set_ext;
delta (==); beta=> x0;
case (x = x0)=> x_x0.
  by subst x0; smt.
  by rewrite mem_rm_neq; smt.
qed.

lemma add_rm_in: forall (x:'a) X,
  mem x X => add x (rm x X) = X
by (intros=> x X x_in_X; apply set_ext; smt).

lemma add_destruct: forall (x:'a) X,
  (exists X', !mem x X' /\ X = add x X') <=> mem x X
by [].

(** single *)
op single:'a -> 'a set.
axiom mem_single_eq: forall (x:'a),
  mem x (single x).
axiom mem_single_neq: forall (x x':'a),
  x <> x' => !mem x (single x').

(** compl *)
op compl:'a set -> 'a set.
axiom mem_compl: forall x (X:'a set),
  mem x (compl X) <=> !mem x X.

lemma complK: forall (X:'a set),
  compl (compl X) = X
by (intros=> X; apply set_ext; smt).

(** univ *)
const univ:'a set = compl empty.
lemma mem_univ: forall (x:'a),
  mem x univ
by [].

(** union *)
op union:'a set -> 'a set -> 'a set.
axiom mem_union: forall x (X1 X2:'a set),
  mem x (union X1 X2) <=> (mem x X1 \/ mem x X2).

lemma unionC: forall (X1 X2:'a set),
  union X1 X2 = union X2 X1
by (intros=> X1 X2; apply set_ext; smt).

lemma unionA: forall (X1 X2 X3:'a set),
  union (union X1 X2) X3 = union X1 (union X2 X3)
by (intros=> X1 X2 X3; apply set_ext; smt).

lemma union0s: forall (X:'a set),
  union empty X = X
by (intros=> X; apply set_ext; smt).

lemma unionLs: forall (X1 X2:'a set),
  X1 <= union X1 X2
by [].

lemma unionK: forall (X:'a set),
  union X X = X
by (intros=> X; apply set_ext; smt).

lemma unionNs: forall (X:'a set),
  union X (compl X) = univ
by (intros=> X; apply set_ext; smt).

lemma union1s: forall (X:'a set),
  union univ X = univ
by (intros=> X; apply set_ext; smt).

(** inter *)
op inter:'a set -> 'a set -> 'a set.
axiom mem_inter: forall x (X1 X2:'a set),
  mem x (inter X1 X2) <=> (mem x X1 /\ mem x X2).

lemma interC: forall (X1 X2:'a set),
  inter X1 X2 = inter X2 X1
by (intros=> X1 X2; apply set_ext; smt).

lemma interA: forall (X1 X2 X3:'a set),
  inter (inter X1 X2) X3 = inter X1 (inter X2 X3)
by (intros=> X1 X2 X3; apply set_ext; smt).

lemma interGs: forall (X1 X2:'a set),
  inter X1 X2 <= X1
by [].

lemma interK: forall (X:'a set),
  inter X X = X
by (intros=> X; apply set_ext; smt).

lemma inter0s: forall (X:'a set),
  inter empty X = empty
by (intros=> X; apply set_ext; smt).

lemma inter1s: forall (X:'a set),
  inter X univ = X
by (intros=> X; apply set_ext; smt).

(** all *)
op all:'a cpred -> 'a set -> bool.
axiom all_def: forall (p:'a cpred) X,
  all p X <=> (forall x, mem x X => p x).

(** any *)
op any:'a cpred -> 'a set -> bool.
axiom any_def: forall (p:'a cpred) X,
  any p X <=> (exists x, mem x X /\ p x).

(** filter *)
op filter:'a cpred -> 'a set -> 'a set.
axiom mem_filter: forall x (p:'a cpred) X,
  mem x (filter p X) <=> (mem x X /\ p x).

lemma filter_cpTrue: forall (X:'a set),
  filter cpTrue X = X
by (intros=> X; apply set_ext; smt).

lemma filter_cpEq_in: forall (x:'a) X,
  mem x X => filter (cpEq x) X = single x
by (intros=> x X x_in_X; apply set_ext; smt).

lemma leq_filter: forall (p:'a cpred) X,
  filter p X <= X
by [].

theory Duni.
  require import Distr.
  (** We recall notations from Distr.ec used here:
      - U denotes a uniformity axiom or lemma,
      - in_d denotes a support membership test,
      - d_x is the weight of x in d,
      - weight_d is the weight of the constantly true predicate in d. *)
  op duni: 'a set -> 'a distr.

  axiom in_duni: forall (x:'a) X, in_supp x (duni X) <=> mem x X.

  axiom duniU: forall (X:'a set) x y,
    mem x X => mem y X =>
    mu_x (duni X) x = mu_x (duni X) y.

  axiom duni_x_nin: forall (x:'a) X, 
    !mem x X => mu_x (duni X) x = 0%r.

  axiom mu_empty: forall (P:'a cpred), mu (duni empty) P = 0%r.

  axiom weight_duni: forall (X:'a set),
    weight (duni X) = if X = empty then 0%r else 1%r.
end Duni.