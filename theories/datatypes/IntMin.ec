(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore Int.
require (*--*) Ring StdOrder.
(*---*) import Ring.IntID StdOrder.IntOrder.

(* -------------------------------------------------------------------- *)
op argmin (f : int -> 'a) (p : 'a -> bool) =
  choiceb (fun j => 0 <= j /\ p (f j) /\ forall i, 0 <= i < j => !p (f i)) 0.

lemma argmin_out (f : int -> 'a) p: (forall i, 0 <= i => !p (f i)) => argmin f p = 0.
proof.
move=> pN; rewrite /argmin choiceb_dfl => //= x; rewrite !negb_and -implybE => le0x.
by rewrite -implybE => px; move: (pN _ le0x).
qed.

lemma nosmt argminP_r (f : int -> 'a) p i: 0 <= i => p (f i) =>
     0 <= argmin f p
  /\ p (f (argmin f p))
  /\ forall i, 0 <= i < (argmin f p) => !p (f i).
proof.
pose F := fun i0 => forall j, 0 <= j < i0 => !p (f j).
move=> ge0_i pi; have: exists j, 0 <= j /\ p (f j) /\ F j.
  elim/sintind: i ge0_i pi => i ge0_i ih pi.
  case: (exists j, (0 <= j < i) /\ p (f j)).
    by case=> j [/ih {ih} ih/ih]; apply.
  move=> h; exists i; rewrite pi ge0_i => j lt_ji; apply/negP.
  by move=> pj; apply/h; exists j; rewrite pj.
by move/choicebP/(_ 0); apply.
qed.

lemma argminP (f : int -> 'a) p i: 0 <= i => p (f i) => p (f (argmin f p)).
proof. by move=> ge0_i/(argminP_r _ _ _ ge0_i). qed.

lemma ge0_argmin (f : int -> 'a) p: 0 <= argmin f p.
proof.                          (* FIXME: choice_spec *)
case: (exists i, 0 <= i /\ p (f i)); first by case=> i [] /(argminP_r f p) h /h.
move=> h; rewrite /argmin choiceb_dfl ?lez_lt_asym //=.
by move=> x; apply/negP=> [# ge0_x px xmin]; apply/h; exists x.
qed.

lemma argmin_min (f : int -> 'a) p: forall j, 0 <= j < argmin f p => !p (f j).
proof.                          (* FIXME: choice_spec *)
case: (exists i, 0 <= i /\ p (f i)); first by case=> i [] /(argminP_r f p) h /h.
move=> h j; rewrite /argmin choiceb_dfl ?lez_lt_asym //=.
by move=> x; apply/negP=> [# ge0_x px xmin]; apply/h; exists x.
qed.

lemma argmin_eq ['a] f p i :
  0 <= i => p (f i) => (forall j, 0 <= j < i => !p (f j)) => argmin<:'a> f p = i.
proof.
move=> ge0_i pfi Npfj @/argmin.
pose Q j := 0 <= j /\ p (f j) /\ forall i, 0 <= i < j => !p (f i).
have /# := choicebP Q 0 _; first by exists i.
qed.

lemma le_argmin ['a] f p i :
  0 <= i =>
  ((exists j, (0 <= j) /\ (p (f j))) => (exists j, (0 <= j <= i) /\ (p (f j)))) <=>
  (argmin<:'a> f p <= i).
proof.
move => le0i; case (exists j, (0 <= j) /\ (p (f j))) => /= [[j [le0j pj]]|].
+ split => [|le_i]; last by exists (argmin f p); rewrite le_i ge0_argmin /=; apply/(argminP _ _ j).
  move => [k [[le0k leki] pk]]; apply/lezNgt/negP => lti_; apply/(argmin_min f p k) => //.
  by split => // _; apply/(ler_lt_trans i).
by move => /negb_exists /= Npj; rewrite argmin_out // => j; move: (Npj j); rewrite negb_and -implybE.
qed.

lemma ge_argmin ['a] f p i :
  0 < i =>
  ((exists j, (0 <= j) /\ (p (f j))) /\ (forall j, (0 <= j < i) => !(p (f j)))) <=>
  (i <= argmin<:'a> f p).
proof.
move => lt0i; case (exists j, (0 <= j) /\ (p (f j))) => /= [[j [le0j pj]]|].
+ split => [|lei_ k [le0k ltki]]; last by apply argmin_min; rewrite le0k /=; apply (ltr_le_trans i).
  move => Npk; apply/lezNgt/negP => lt_i; apply (Npk (argmin f p)); first by rewrite lt_i ge0_argmin.
  by apply (argminP _ _ j).
move => /negb_exists /= Npj; apply/ltrNge; rewrite argmin_out // => j.
by move: (Npj j); rewrite negb_and -implybE.
qed.

lemma argmin_le ['a] f p q :
  (exists j, (0 <= j) /\ (p (f j))) =>
  (forall j, 0 <= j => p (f j) => q (f j)) =>
  argmin<:'a> f q <= argmin<:'a> f p.
proof.
move=> pj le_pq; apply/le_argmin; first by apply/ge0_argmin.
move=> [j [le0j qj]]; exists (argmin f p); rewrite ge0_argmin /=.
by apply le_pq; [rewrite ge0_argmin|move: pj => [k [le0k pk]]; apply (argminP _ _ k)].
qed.

(* -------------------------------------------------------------------- *)
abbrev minz = argmin (fun (i : int) => i).

(* -------------------------------------------------------------------- *)
op argmax ['a] (f : int -> 'a) (p : 'a -> bool) : int =
  choiceb (fun (j : int) => 0 <= j /\ p (f j) /\ forall (i : int), j < i => ! p (f i)) 0.

lemma argmax_out (f : int -> 'a) p:
(forall i, 0 <= i => !p (f i)) \/
(forall i, 0 <= i => exists j, i <= j /\ p (f j)) =>
argmax f p = 0.
proof.
move=> [pN|pij]; rewrite /argmax choiceb_dfl => //= x; rewrite !negb_and -implybE => le0x; rewrite -implybE => px; first by move: (pN _ le0x).
by rewrite negb_forall /=; move: (pij (x + 1) _); [rewrite addz_ge0|move => [j [lejx pj]]; exists j; rewrite negb_imply ltzE].
qed.

lemma argmaxP_r (f : int -> 'a) p i j:
  0 <= i =>
  0 <= j =>
  p (f i) =>
  (forall k, j <= k => !(p (f k))) =>
     0 <= argmax f p
  /\ p (f (argmax f p))
  /\ forall i, (argmax f p) < i => !p (f i).
proof.
pose F := fun i0 => forall (j : int), i0 < j => !p (f j).
move=> ge0_i ge0_j pi pnj; have: exists k, 0 <= k /\ p (f k) /\ F k.
  elim/sintind: j ge0_j pnj => j ge0_j ih pnj.
  case: (exists k, (0 <= k < j) /\ (forall (l : int), k <= l => ! p (f l))); first by case=> k [/ih].
  move=> h; exists (j-1); apply/and_impr; split => [|le0_]; [|split].
    by move/ler_eqVlt: ge0_j => [<<-|]; [move: (pnj i); rewrite ge0_i pi|move/ltzE/ler_subr_addr].
    by apply/negbNE/negP => pn_; apply/h; exists (j-1); rewrite le0_ ltzE //= => l /ler_eqVlt [<<- //|/ltzE /= /pnj].
  by move => k /ltzE /=; apply pnj.
by move/choicebP/(_ 0); apply.
qed.

lemma argmaxP (f : int -> 'a) p i j:
  0 <= i =>
  0 <= j =>
  p (f i) =>
  (forall k, j <= k => !(p (f k))) =>
  p (f (argmax f p)).
proof. by move => ge0i ge0j Hpfi Hnpfj; move: (argmaxP_r _ _ _ _ _ _ Hpfi Hnpfj). qed.

lemma ge0_argmax (f : int -> 'a) p:
  0 <= argmax f p.
proof.                          (* FIXME: choice_spec *)
case: (exists i j, 0 <= i /\ 0 <= j /\ p (f i) /\ (forall k, j <= k => !(p (f k)))).
+ by case=> i j [? [? [Hpfi Hnpfj]]]; move: (argmaxP_r _ _ _ _ _ _ Hpfi Hnpfj).
move=> h; rewrite /argmax choiceb_dfl ?lez_lt_asym //=.
move=> x; apply/negP=> [# ge0_x px xmax]; apply/h; exists x; exists (x + 1).
by do!split => //; [apply addz_ge0|move => k; rewrite -ltzE; apply xmax].
qed.

lemma argmax_max (f : int -> 'a) p j:
  0 <= j =>
  (forall k, j <= k => !(p (f k))) =>
  forall j, argmax f p < j => !p (f j).
proof.                          (* FIXME: choice_spec *)
case: (exists i, 0 <= i /\ p (f i)).
+ by case=> i [? Hpfi] ? Hnpfj; move: (argmaxP_r _ _ _ _ _ _ Hpfi Hnpfj).
move=> h i; rewrite /argmax choiceb_dfl ?lez_lt_asym //=.
+ by move=> x; apply/negP=> [# le0x Hpfx Hnpfx]; apply/h; exists x.
by move => _ k lt0k; apply/negP => Hpfk; apply/h; exists k; split => //; apply/ltzW.
qed.

lemma argmax_eq ['a] f p i :
  0 <= i => p (f i) => (forall j, i < j => !p (f j)) => argmax<:'a> f p = i.
proof.
move=> ge0_i pfi Npfj @/argmax.
pose Q j := 0 <= j /\ p (f j) /\ forall i, j < i => !p (f i).
by have /# := choicebP Q 0 _; exists i.
qed.

lemma le_argmax ['a] f p i :
  0 <= i =>
  ((exists j, (0 <= j) /\ (forall k, (j <= k) => !(p (f k)))) => (forall j, i < j => !(p (f j)))) <=>
  (argmax<:'a> f p <= i).
proof.
move => le0i; case ((forall i, 0 <= i => !p (f i)) \/ (forall i, 0 <= i => exists j, i <= j /\ p (f j))) => /=.
+ move => Hor; rewrite argmax_out // le0i /=; case Hor => [Npj _ j ltij|]; first by apply/Npj/(lez_trans i) => //; apply ltzW.
  by move => pj [j [le0j Npk]]; case (pj _ le0j) => k [lejk pkj]; move: (Npk _ lejk).
move => /negb_or [/negb_forall [j /= /negb_imply [le0j /= pj]] /negb_forall [k /= /negb_imply [le0k /negb_exists /= Npl]]].
have ->/=: (exists (l : int), 0 <= l /\ forall (m : int), l <= m => ! p (f m)).
+ by exists k; split => // l ltkl; move: (Npl l) => /negb_and; rewrite ltkl.
split => [Npi|le_i l leil].
+ apply/lezNgt/negP => /(Npi _); apply/negP => /=; apply/(argmaxP _ _ _ (i + 1) le0j _ pj _); first by apply addz_ge0.
  by move => l /ltzE; apply Npi.
apply (argmax_max _ _ _ le0k _ _ _); last by apply (ler_lt_trans i) => //.
by move => m lekm; move: (Npl m) => /negb_and; rewrite lekm.
qed.

lemma ge_argmax ['a] f p i :
  0 < i =>
  ((exists j, (0 <= j) /\ (forall k, (j <= k) => !(p (f k)))) /\ (exists j, (i <= j) /\ (p (f j)))) <=>
  (i <= argmax<:'a> f p).
proof.
move => lt0i; case ((forall i, 0 <= i => !p (f i)) \/ (forall i, 0 <= i => exists j, i <= j /\ p (f j))) => /=.
+ move => Hor; rewrite argmax_out // (lezNgt i) lt0i /=; apply/negb_and; case Hor => [Npj|pj].
  - by right; apply/negb_exists => /= j; apply/negb_and/implybE => leij; apply/Npj/(lez_trans i) => //; apply/ltzW.
  left; apply/negb_exists => /= j; apply/negb_and/implybE => le0j; apply/negb_forall; move: (pj _ le0j).
  by move => /= [k [lejk pk]]; exists k; apply/negb_imply; split.
move => /negb_or [/negb_forall [j /= /negb_imply [le0j /= pj]] /negb_forall [k /= /negb_imply [le0k /negb_exists /= Npl]]].
have ->/=: (exists (l : int), 0 <= l /\ forall (m : int), l <= m => ! p (f m)).
+ by exists k; split => // l ltkl; move: (Npl l) => /negb_and; rewrite ltkl.
split => [[l [leil pl]]|lei_]; last by exists (argmax f p); split => //; apply/(argmaxP _ _ _ k le0j le0k pj _) => l lekl; move: (Npl l); rewrite lekl.
apply/lezNgt/negP => lt_i.
(*FIXME: why no one liner? Pierre-Yves*)
have lt_l:= (ltr_le_trans _ _ _ lt_i leil).
by move: (argmax_max _ _ _ le0k _ _ lt_l); [move => m lekm; move: (Npl m); rewrite lekm|].
qed.

lemma argmax_le ['a] f p q :
  (exists j, (0 <= j) /\ (forall k, (j <= k) => !(q (f k)))) =>
  (forall j, 0 <= j => p (f j) => q (f j)) =>
  argmax<:'a> f p <= argmax<:'a> f q.
proof.
move => [i [le0i Nqk]] le_pq; apply le_argmax; first by apply ge0_argmax.
move => [j [le0j Npk]] k /ltzE /ler_subr_addr le__; move: (le__); rewrite -le_argmax.
+ by apply/(lez_trans (argmax f q)) => //; apply/ge0_argmax.
move => HNq; apply/negP => pk; apply (HNq _ k); [by exists i|by apply/ltzE| ].
apply le_pq => //; apply (lez_trans (argmax f q)); first apply ge0_argmax.
by apply (lez_trans (k-1)) => //; apply/ltzW/ltzE.
qed.

(* -------------------------------------------------------------------- *)
abbrev maxz = argmax (fun (i : int) => i).

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

lemma pmin_nmem E i : ! sempty (pcap E) => 0 <= i < pmin E => ! E i.
proof.
move => Hnsempty [le0i ltipmin]; apply/negP => HEi.
by move: (ltr_le_trans _ _ _ ltipmin (pmin_min _ _ Hnsempty le0i HEi)).
qed.

lemma pmin_max E i : ! sempty (pcap E) => 0 <= i => (forall j , 0 <= j < i => ! E j) => i <= pmin E.
proof.
move=> h ge0_i min_i; rewrite lerNgt; apply/negP=> gti.
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
