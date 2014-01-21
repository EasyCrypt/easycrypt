(* --------------------------------------------------------------------
 * Copyright IMDEA Software Institute / INRIA - 2013, 2014
 * -------------------------------------------------------------------- *)

(** Extensional equality for functions *)
(* This is separate from more advanced
   definitions and results on functions
   to avoid sending large amounts of stuff
   to SMT whenever possible. *)
pred (==) (f g:'a -> 'b) = forall x, f x = g x.

lemma nosmt eq_refl (X:'a -> 'b):     X == X by [].
lemma nosmt eq_symm (X Y:'a -> 'b):   X == Y => Y == X by [].
lemma nosmt eq_tran (X Y Z:'a -> 'b): X == Y => Y == Z => X == Z by [].

axiom fun_ext (f g:'a -> 'b): f == g <=> f = g.

(* Congruence when assumption is extensional *)
lemma congr_ext (f g:'a -> 'b) (x y:'a):
  f == g => x = y => f x = g y
by rewrite fun_ext=> -> ->.

(* We need to have these two explicit, since = is not an operator *)
lemma eqL (x:'a): (fun y, x = y) = (=) x
by apply fun_ext.

lemma eqR (y:'a): (fun x, x = y) = (=) y
by (apply fun_ext=> x //=; rewrite (eq_sym x)).
