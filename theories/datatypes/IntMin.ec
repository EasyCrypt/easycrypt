(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore Int.
require (*--*) Ring StdOrder.
(*---*) import Ring.IntID StdOrder.IntOrder.

(* -------------------------------------------------------------------- *)
op pcap (E : int -> bool) =
  fun x => 0 <= x /\ E x.

op pmin_spec (E : int -> bool) =
  fun x => pcap E x /\ forall y, pcap E y => x <= y.

op pmin (E : int -> bool) =
  choiceb (pmin_spec E) 0.

lemma pmin_spec E :
  !sempty (pcap E) => exists x, pmin_spec E x.
proof.
apply: contraR; rewrite negb_exists /= => h x.
move: {-2}x (lerr x); elim/ge0ind: x.
+ by move=> n @/pcap lt0_n x /ler_lt_trans /(_ _ lt0_n) /ltrNge ->.
+ move=> x; rewrite ler_eqVlt => @/pcap -[->/=|/ltrNge ->//].
  by have := h 0; apply: contra => @/pmin_spec @/pcap -> /= y [].  
move=> n ge0_n ih x; rewrite ler_eqVlt => -[->|]; last first.
+ by rewrite ltzS; apply/ih.
have := h (n + 1); apply: contra => @/pmin_spec @/pcap -[-> ->] /=.
by move=> y [ge0_y Ey]; rewrite lerNgt ltzS; apply/negP=> /ih.
qed.

lemma pmin_mem (E : int -> bool) :
  !sempty (pcap E) => E (pmin E).
proof.
move/pmin_spec/choicebP/(_ 0) => /=.
by rewrite -/(pmin E); case=> -[].
qed.

lemma pmin_min (E : int -> bool) x :
  !sempty (pcap E) => 0 <= x => E x => pmin E <= x.
proof.
move/pmin_spec/choicebP/(_ 0) => /=.
by rewrite -/(pmin E); case=> _ hmin ge0_x Ex; apply: hmin.
qed.
