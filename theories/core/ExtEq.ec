(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* Extensional equality for functions.
 *
 * This is separate from more advanced definitions and results on
 * functions to avoid sending large amounts of stuff to SMT whenever
 * possible.
 *)

(* -------------------------------------------------------------------- *)
pred (==) (f g:'a -> 'b) = forall x, f x = g x.

(* -------------------------------------------------------------------- *)
lemma nosmt frefl  (f     : 'a -> 'b): f == f by [].
lemma nosmt fsym   (f g   : 'a -> 'b): f == g => g == f by [].
lemma nosmt ftrans (f g h : 'a -> 'b): f == g => g == h => f == h by [].

(* -------------------------------------------------------------------- *)
axiom fun_ext ['a 'b] (f g:'a -> 'b): f == g <=> f = g.

(* -------------------------------------------------------------------- *)
lemma econgr1 ['a 'b] (f g : 'a -> 'b) x y: f == g => x = y => f x = g y.
proof. by move/fun_ext=> -> ->. qed.

(* -------------------------------------------------------------------- *)
lemma eqL (x:'a): (fun y => x = y) = (=) x.
proof. by apply fun_ext. qed.

lemma eqR (y:'a): (fun x => x = y) = (=) y.
proof. by apply fun_ext=> x; rewrite (eq_sym x). qed.
