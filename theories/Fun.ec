(** Extensional equality for functions *)
pred (==) (f g:'a -> 'b) = forall x, f x = g x.

lemma nosmt eq_refl (X:'a -> 'b):     X == X by [].
lemma nosmt eq_symm (X Y:'a -> 'b):   X == Y => Y == X by [].
lemma nosmt eq_tran (X Y Z:'a -> 'b): X == Y => Y == Z => X == Z by [].

axiom fun_ext (f g:'a -> 'b): f == g <=> f = g.

(* We need to have these two explicit, since = is not an operator *)
lemma eqL (x:'a): (fun y, x = y) = (=) x
by apply fun_ext.

lemma eqR (y:'a): (fun x, x = y) = (=) y
by (apply fun_ext=> x //=; rewrite (eq_sym x)).

(*** Working with predicates *)
(** Inclusion order *)
pred (<=) (p q:'a -> bool) =
  forall (a:'a), p a => q a.

lemma nosmt leq_refl (X Y:'a -> bool):
  X = Y => X <= Y
by [].

lemma nosmt leq_asym (X Y:'a -> bool):
  X <= Y => Y <= X => X = Y
by (rewrite -fun_ext; smt).

lemma nosmt leq_tran (X Y Z:'a -> bool):
  X <= Y => Y <= Z => X <= Z
by [].

pred (>=) (p q:'a -> bool) = q <= p.
pred (<)  (p q:'a -> bool) = p <= q /\ p <> q.
pred (>)  (p q:'a -> bool) = p >= q /\ p <> q.

(** Lifting boolean operators to predicates *)
op True (x:'a) : bool = true.
op False (x:'a): bool = false.

op [!]  (p:'a -> bool)  : 'a -> bool = fun x, !p x.
op (/\) (p q:'a -> bool): 'a -> bool = fun x, p x /\ q x.
op (\/) (p q:'a -> bool): 'a -> bool = fun x, p x \/ q x.

(** Lemmas *)
lemma True_true (x:'a): True x by done.

lemma True_unique (p:'a -> bool): (forall x, p x) => p = True.
proof strict.
by rewrite -fun_ext=> px x; rewrite px.
qed.

lemma False_false (x:'a): !False x by [].

lemma False_unique (p:'a -> bool): (forall x, !p x) => p = False.
proof strict.
by rewrite -fun_ext=> px x; rewrite /False neqF px.
qed.

lemma Not_not (p:'a -> bool) x: (!p) x <=> !p x by [].

lemma And_and (p q:'a -> bool) x: (p /\ q) x <=> (p x /\ q x) by [].

lemma Or_or (p q:'a -> bool) x: (p \/ q) x <=> (p x \/ q x) by [].

lemma Excluded_Middle (p:'a -> bool): ((!p) \/ p) = True
by (apply fun_ext; smt).

lemma Sound (p:'a -> bool): ((!p) /\ p) = False
by (apply fun_ext; smt).

lemma congr_ext (f g:'a -> 'b) (x y:'a):
  f == g => x = y => f x = g y
by [].

lemma And_leq_l (p q:'a -> bool): (p /\ q) <= p by [].

lemma And_leq_r (p q:'a -> bool): (p /\ q) <= q by [].
 
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
