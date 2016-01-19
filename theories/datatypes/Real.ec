(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int Ring AlgTactic.

op zero  : real.
op one   : real.
op ( + ) : real -> real -> real.
op [ - ] : real -> real.
op ( * ) : real -> real -> real.
op inv   : real -> real.

op ( <  ) : real -> real -> bool.
op ( <= ) = fun x y => x < y \/ x = y.

abbrev ( - ) (x y : real) = x + -y.
abbrev ( / ) (x y : real) = x * (inv y).

abbrev [-printing] ( >  ) (x y : real) = y < x.
abbrev [-printing] ( >= ) (x y : real) = y <= x.

(* -------------------------------------------------------------------- *)
op from_int: int -> real.

lemma divr0: forall x, x / from_int 0 = from_int 0 by done.
lemma invr0: inv (from_int 0) = from_int 0 by done.

(* -------------------------------------------------------------------- *)
op b2r (b:bool) = if b then from_int 1 else from_int 0.

(* -------------------------------------------------------------------- *)
op "`|_|" x = if from_int 0 <= x then x else -x.

op ( ^ )  : real -> int -> real.

axiom powrN (x : real) (n : int) :
  x^(-n) = inv (x^n).

axiom powr0 (x : real) :
  x^0 = one.

axiom powrS (x : real) (n : int) :
  0 <= n => x^(n+1) = x^n * x.

(* -------------------------------------------------------------------- *)
(* WARNING Lemmas used by tactics :
   eq_le addleM real_le_trans and the following lemmas *)
lemma nosmt upto2_abs (x1 x2 x3 x4 x5:real):
   from_int 0 <= x1 =>
   from_int 0 <= x3 =>
   x1 <= x5 =>
   x3 <= x5 =>
   x2 = x4 =>
   `|x1 + x2 - (x3 + x4)| <= x5 by smt full.

lemma nosmt upto2_notbad (ev1 ev2 bad1 bad2:bool) :
  ((bad1 <=> bad2) /\ (!bad2 => (ev1 <=> ev2))) =>
  ((ev1 /\ !bad1) <=> (ev2 /\ !bad2)) by smt.

lemma nosmt upto2_imp_bad (ev1 ev2 bad1 bad2:bool) :
  ((bad1 <=> bad2) /\ (!bad2 => (ev1 <=> ev2))) =>
  (ev1 /\ bad1) => bad2 by smt.

lemma nosmt upto_bad_false (ev bad2:bool) :
  !((ev /\ !bad2) /\ bad2) by smt.

lemma nosmt upto_bad_or (ev1 ev2 bad2:bool) :
   (!bad2 => ev1 => ev2) => ev1 =>
    ev2 /\ !bad2 \/ bad2 by smt.

lemma nosmt upto_bad_sub (ev bad:bool) :
  ev /\ ! bad => ev by [].
