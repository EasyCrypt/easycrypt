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
proof. by move/pmin_spec/choicebP/(_ 0) => /=; do 2! case. qed.

lemma pmin_min (E : int -> bool) x :
  !sempty (pcap E) => 0 <= x => E x => pmin E <= x.
proof.
move/pmin_spec/choicebP/(_ 0) => /=.
by rewrite -/(pmin E); case=> _ hmin ge0_x Ex; apply: hmin.
qed.

lemma pmin_empty E : sempty (pcap E) => pmin E = 0.
proof.
move=> h; rewrite /pmin choiceb_dfl //.
rewrite -negb_exists /=; apply: contraL h.
by case=> i [??]; apply/semptyNP; exists i.
qed.

lemma ge0_pmin E : 0 <= pmin E.
proof.
case: (sempty (pcap E)); first by move/pmin_empty=> ->.
by move/pmin_spec/choicebP/(_ 0) => /=; do 2! case.
qed.

lemma pmin_eq (E : int -> bool) (i : int) :
  0 <= i => E i => (forall j, 0 <= j < i => !E j) => pmin E = i.
proof.
move=> ge0_i Ei min_i; have h: !sempty (pcap E).
- by apply/semptyNP; exists i.
rewrite eqr_le pmin_min //= lerNgt; apply/negP=> gti.
by apply/(min_i (pmin E))/pmin_mem => //; rewrite ge0_pmin.
qed.

(* -------------------------------------------------------------------- *)
op fmin_spec ['a] (f : 'a -> int) (p : 'a -> bool) (x : 'a) =
  0 <= f x /\ p x /\ forall y, 0 <= f y => p y => f x <= f y.

op fmin ['a] f p = choiceb (fmin_spec<:'a> f p) witness.

lemma fminP ['a] (f : 'a -> int) (p : 'a -> bool) :
  (exists x, 0 <= f x /\ p x) =>
    0 <= f (fmin f p) /\ p (fmin f p) /\
      forall y, 0 <= f y => p y => f (fmin f p) <= f y.
proof.
case=> x [ge0_fx px]; apply: (choicebP (fmin_spec f p) witness).
suff h: forall n, 0 <= n => forall x, n = f x => p x =>
  exists y, fmin_spec f p y by apply: (h (f x) _ x).
elim/sintind=> {x ge0_fx px} i ge0_i ih x ->> px.
case: (exists y, 0 <= f y /\ p y /\ f y < f x) => [[y [# 3?]]|].
- by apply: (ih (f y) _ y).
rewrite negb_exists /= => hx; exists x; do! split => //.
by move=> y ge0_fy py; have := hx y; rewrite ge0_fy py /= ltrNge.
qed.
