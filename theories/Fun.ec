(** Extensional equality for functions *)
pred (==) (f g:'a -> 'b) = forall x, f x = g x.

lemma nosmt eq_refl: forall (X:'a -> 'b), X == X by [].
lemma nosmt eq_symm: forall (X Y:'a -> 'b), X == Y => Y == X by [].
lemma nosmt eq_tran: forall (X Y Z:'a -> 'b), X == Y => Y == Z => X == Z by [].

axiom fun_ext: forall (f g:'a -> 'b), f == g => f = g.

(* We need to have these two explicit, since = is not an operator *)
lemma eqL (x:'a): (fun y, x = y) = (=) x
by apply fun_ext.

lemma eqR (y:'a): (fun x, x = y) = (=) y
by (apply fun_ext=> x //=; rewrite (rw_eq_sym x)).

(** Computable predicates *)
type 'a cpred = 'a -> bool.
pred (<=) (p q:'a cpred) = forall (a:'a), p a => q a.

lemma nosmt leq_refl: forall (X Y:'a cpred), X = Y => X <= Y by [].
lemma nosmt leq_asym: forall (X Y:'a cpred),
  X <= Y => Y <= X => X = Y
by (intros=> X Y X_leq_Y Y_leq_X; apply fun_ext; smt).
lemma nosmt leq_tran: forall (X Y Z:'a cpred), X <= Y => Y <= Z => X <= Z by [].

pred (>=) (p q:'a cpred) = q <= p.
pred (<)  (p q:'a cpred) = p <= q /\ p <> q.
pred (>)  (p q:'a cpred) = p >= q /\ p <> q.

(** Operators on predicates *)
op cpTrue (x:'a) : bool = true.
op cpFalse (x:'a) : bool = false.

op cpNot(p:'a cpred, x:'a) : bool = !p x.
op cpAnd(p q:'a cpred, x:'a) : bool = p x /\ q x.
op cpOr(p q:'a cpred, x:'a) : bool = p x \/ q x.

(** Lemmas *)
lemma cpTrue_true : forall (x:'a), cpTrue x by [].

lemma cpTrue_def (p:'a cpred): (forall x, p x) => p = cpTrue.
proof strict.
by intros=> px; apply fun_ext=> x; rewrite px.
qed.

lemma cpFalse_false : forall (x:'a), !cpFalse x by [].

lemma cpFalse_def (p:'a cpred): (forall x, !p x) => p = cpFalse
by [].

lemma cpNot_not : forall (p:'a cpred) x, cpNot p x <=> !p x by [].
lemma cpAnd_and :
  forall (p q:'a cpred) (x:'a), cpAnd p q x <=> (p x /\ q x) by [].
lemma cpOr_or :
  forall (p q:'a cpred) (x:'a), cpOr p q x <=> (p x \/ q x) by [].

lemma cpEM: forall (p: 'a cpred),
  cpOr (cpNot p) p = cpTrue
by (intros p; apply fun_ext; smt).

lemma cpC: forall (p: 'a cpred),
  cpAnd (cpNot p) p = cpFalse.
proof strict.
intros=> p; apply fun_ext; smt.
qed.

lemma congr_fun_app : forall (f g : 'a -> 'b) (x y : 'a),
  f == g => x = y => f x = g y.
proof.
 intros => f g x y heqf ->.
 by rewrite (fun_ext f g _).
qed.
 
(*
(** Properties of functions *)
op id (x:'a): 'a = x.

op compose: ('b -> 'c) -> ('a -> 'b) -> ('a -> 'c).
axiom compose_def: forall (f:'a -> 'b) (g:'b -> 'c) (x:'a),
  compose g f x = g (f x).

pred injective (f:'a -> 'b) =
  forall (x y:'a), f x = f y => x = y.

pred cancel (f:'a -> 'b) (g:'b -> 'a) =
  compose g f = id.

pred pcancel (f:'a -> 'b) (g:'b -> 'a) (p:'b -> bool) =
  forall (x:'a), p (f x) /\ compose g f x = x.

pred ocancel (f:'a -> 'b) (g:'b -> 'a) (p:'a -> bool) =
  forall (x:'a), p x => compose g f x = x.

pred bijective (f:'a -> 'b) =
  exists (g:'b -> 'a), cancel f g /\ cancel g f.

pred involutive (f:'a -> 'a) = cancel f f.

(** Properties of operators *)
pred left_id (e:'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o e x = x.

pred right_id (e:'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o x e = x.

pred left_inverse (e:'a) (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o (inv x) x = e.

pred right_inverse (e:'a) (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o x (inv x) = e.

pred self_inverse (e:'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o x x = e.

pred idempotent (o:'a -> 'a -> 'a) =
  forall (x:'a), o x x = x.

pred associative (o:'a -> 'a -> 'a) =
  forall (x y z:'a), o x (o y z) = o (o x y) z.

pred commutative (o:'a -> 'a -> 'a) =
  forall (x y:'a),  o x y = o y x.

pred left_commutative (o:'a -> 'a -> 'a) =
  forall (x y z:'a), o x (o y z) = o y (o x z).

pred right_commutative (o:'a -> 'a -> 'a) =
  forall (x y z:'a), o (o x y) z = o (o x z) y.

pred left_zero (z:'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o z x = x.

pred right_zero (z:'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o x z = x.

pred left_distributive (o1:'a -> 'a -> 'a) (o2:'a -> 'a -> 'a) =
  forall (x y z:'a), o1 (o2 x y) z = o2 (o1 x z) (o1 y z).

pred right_distributive (o1:'a -> 'a -> 'a) (o2:'a -> 'a -> 'a) =
  forall (x y z:'a), o1 x (o2 y z) = o2 (o1 x y) (o1 x y).

pred interchange (o1:'a -> 'a -> 'a) (o2:'a -> 'a -> 'a) =
  forall (x y z t:'a), o1 (o2 x y) (o2 z t) = o2 (o1 x z) (o1 y t).

pred left_injective (o:'a -> 'a -> 'a) =
  forall (x y z:'a), o x y = o z y => x = z.

pred right_injective (o:'a -> 'a -> 'a) =
  forall (x y z:'a), o x y = o x z => y = z.

pred left_loop (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x y:'a), o (inv x) (o x y) = y.

pred rev_left_loop (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x y:'a), o x (o (inv x) y) = y.

pred right_loop (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x y:'a), o (o x y) (inv y) = x.

pred rev_right_loop (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x y:'a), o (o x (inv y)) y = x.
*)
