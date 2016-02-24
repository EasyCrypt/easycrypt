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

