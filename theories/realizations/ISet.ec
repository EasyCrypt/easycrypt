require import Int.
require import Fun.

(** We realize potentially infinite sets as boolean functions *)
(* We avoid using maps as they depend on infinite sets *)
type 'a set = 'a cpred.

(** We use membership as core specification *)
op mem (x:'a) (X:'a set) = X x.

(** Functional extension is an equivalence relation *)
(* Symbols are shared with Fun *)
lemma nosmt eq_refl: forall (X:'a set), X == X by [].
lemma nosmt eq_symm: forall (X Y:'a set), X == Y => Y == X by [].
lemma nosmt eq_tran: forall (X Y Z:'a set), X == Y => Y == Z => X == Z by [].

(* And we can use it as equality *)
axiom set_ext: forall (X1 X2:'a set), X1 == X2 => X1 = X2.

(** Functional inclusion is a partial order *)
(* Symbols are shared with Fun *)
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

(** mem *)
op empty = cpFalse<:'a>.
lemma mem_empty: forall (x:'a), !(mem x empty) by [].

(** add *)
op add (x:'a) (X:'a set) = lambda y, (x = y) || X y.
lemma mem_add: forall (x y:'a) X,
  (mem x (add y X)) = (mem x X \/ x = y)
by [].

(** rm *)
op rm (x:'a) (X:'a set) = lambda y, (x <> y) && X y.
lemma mem_rm_eq: forall (x:'a) X,
  !(mem x (rm x X))
by [].
lemma mem_rm_neq: forall (x x':'a) X,
  x <> x' => mem x (rm x' X) = mem x X
by [].

(** single *)
op single (x:'a) = (=) x.
lemma mem_single_eq: forall (x:'a),
  mem x (single x)
by [].
lemma mem_single_neq: forall (x x':'a),
  x <> x' => !mem x (single x')
by [].

(** compl *)
op compl (X:'a set) = cpNot X.
lemma mem_compl: forall x (X:'a set),
  mem x (compl X) <=> !mem x X
by [].

(** univ *)
op univ:'a set = cpTrue.
lemma univ_n0: univ<:'a> = compl empty
by (apply set_ext; smt).

(** union *)
op union = cpOr<:'a>.
lemma mem_union: forall x (X1 X2:'a set),
  mem x (union X1 X2) <=> (mem x X1 \/ mem x X2)
by [].

(** inter *)
op inter = cpAnd<:'a>.
lemma mem_inter: forall x (X1 X2:'a set),
  mem x (inter X1 X2) <=> (mem x X1 /\ mem x X2)
by [].

(** all *)
op all (p:'a cpred) (X:'a set) = (inter p X) = X.
lemma all_def: forall (p:'a cpred) X,
  all p X <=> (forall x, mem x X => p x).
proof strict.
intros=> p X; delta mem all inter cpAnd; beta; split=> h.
  rewrite -h=> //.
  apply set_ext; delta (==); beta=> x.
  cut ->: (p x /\ X x) <=> X x; last by trivial.
    by split=> // h0; split=> //; apply h=> //.
qed.

(** any *)
op any (p:'a cpred) (X:'a set) = (inter p X) <> empty.
lemma any_def: forall (p:'a cpred) X,
  any p X <=> (exists x, mem x X /\ p x).
proof strict.
intros=> p X; delta mem any inter cpAnd; beta; split=> h; last smt.
  cut h1: exists x, (lambda x, p x /\ X x) x. (* This proof is disgusting *)
    generalize h; apply absurd; simplify=> h; apply set_ext; smt.
    elim h1; beta=> {h1} x x_in_inter; exists x; smt.
qed.

(** filter *)
op filter (p:'a cpred) (X:'a set) = inter p X.
lemma mem_filter: forall x (p:'a cpred) X,
  mem x (filter p X) <=> (mem x X /\ p x)
by [].

op create (x:'a cpred) : 'a set = x.
lemma mem_create :
  forall (x:'a) p,
    mem x (create p) = p x by trivial.