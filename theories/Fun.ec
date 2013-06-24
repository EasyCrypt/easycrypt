(** Extensional equality for functions *)
pred (==) (f g:'a -> 'b) = forall x, f x = g x.

lemma local eq_refl: forall (X:'a -> 'b), X == X by [].
lemma local eq_symm: forall (X Y:'a -> 'b), X == Y => Y == X by [].
lemma local eq_tran: forall (X Y Z:'a -> 'b), X == Y => Y == Z => X == Z by [].

axiom fun_ext: forall (f g:'a -> 'b), f == g => f = g.

(** Computable predicates *)
type 'a cpred = 'a -> bool.
pred (<=) (p q:'a cpred) = forall (a:'a), p a => q a.

lemma local leq_refl: forall (X:'a cpred), X <= X by [].
lemma local leq_asym: forall (X Y:'a cpred),
  X <= Y => Y <= X => X = Y
by (intros=> X Y X_leq_Y Y_leq_X; apply fun_ext; smt).
lemma local leq_tran: forall (X Y Z:'a cpred), X <= Y => Y <= Z => X <= Z by [].

pred (>=) (p q:'a cpred) = q <= p.
pred (<)  (p q:'a cpred) = p <= q /\ p <> q.
pred (>)  (p q:'a cpred) = p >= q /\ p <> q.

(** Operators on predicates *)
op cpTrue (x:'a) : bool = true.
op cpFalse (x:'a) : bool = false.
op cpEq (x:'a) : 'a -> bool = (=) x.

op cpNot(p:'a cpred, x:'a) : bool = !p x.
op cpAnd(p q:'a cpred, x:'a) : bool = p x /\ q x.
op cpOr(p q:'a cpred, x:'a) : bool = p x \/ q x.

(** Lemmas *)
lemma cpTrue_true : forall (x:'a), cpTrue x by [].
lemma cpFalse_false : forall (x:'a), !cpFalse x by [].

lemma cpNot_not : forall (p:'a cpred) x, cpNot p x <=> !p x by [].
lemma cpAnd_and :
  forall (p q:'a cpred) (x:'a), cpAnd p q x <=> (p x /\ q x) by [].
lemma cpOr_or :
  forall (p q:'a cpred) (x:'a), cpOr p q x <=> (p x \/ q x) by [].

lemma cpEM: forall (p: 'a cpred),
  cpOr (cpNot p) p = cpTrue
by (intros p; apply fun_ext; smt).
