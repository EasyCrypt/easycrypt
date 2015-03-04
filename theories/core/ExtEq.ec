(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(** Extensional equality for functions *)
(* This is separate from more advanced
   definitions and results on functions
   to avoid sending large amounts of stuff
   to SMT whenever possible. *)
pred (==) (f g:'a -> 'b) = forall x, f x = g x.

lemma nosmt frefl  (X:'a -> 'b):     X == X by [].
lemma nosmt fsym   (X Y:'a -> 'b):   X == Y => Y == X by [].
lemma nosmt ftrans (X Y Z:'a -> 'b): X == Y => Y == Z => X == Z by [].

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
