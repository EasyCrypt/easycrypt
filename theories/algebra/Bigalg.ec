(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

pragma +implicits.

(* -------------------------------------------------------------------- *)
require import AllCore List StdOrder.
require (*--*) Bigop Ring Number.

import Ring.IntID.

(* -------------------------------------------------------------------- *)
abstract theory BigZModule.
type t.

clone import Ring.ZModule as ZM with type t <- t.
clear [ZM.* ZM.AddMonoid.*].

clone include Bigop with
  type t <- t,
  op   Support.idm <- ZM.zeror,
  op   Support.(+) <- ZM.(+)

  proof Support.Axioms.*.

realize Support.Axioms.addmA. by apply/addrA. qed.
realize Support.Axioms.addmC. by apply/addrC. qed.
realize Support.Axioms.add0m. by apply/add0r. qed.

(* -------------------------------------------------------------------- *)
lemma sumrD P F1 F2 (r : 'a list):
  (big P F1 r) + (big P F2 r) = big P (fun x => F1 x + F2 x) r.
proof. by rewrite big_split. qed.

(* -------------------------------------------------------------------- *)
lemma sumrN P F (r : 'a list):
  - (big P F r) = (big P (fun x => -(F x)) r).
proof. by apply/(big_endo oppr0 opprD). qed.

(* -------------------------------------------------------------------- *)
lemma sumrB P F1 F2 (r : 'a list):
  (big P F1 r) - (big P F2 r) = big P (fun x => F1 x - F2 x) r.
proof. by rewrite sumrN sumrD; apply/eq_bigr => /=. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt sumr_const (P : 'a -> bool) x s:
  big P (fun _ => x) s = intmul x (count P s).
proof. by rewrite big_const intmulpE 1:count_ge0 // -ZM.AddMonoid.iteropE. qed.

lemma sumri_const k (n m:int) : n <= m => bigi predT (fun _ => k) n m = intmul k (m - n).
proof. by move=> h; rewrite sumr_const count_predT size_range /#. qed.

(* -------------------------------------------------------------------- *)
lemma sumr_undup ['a] (P : 'a -> bool) F s :
  big P F s = big P (fun a => intmul (F a) (count (pred1 a) s)) (undup s).
proof.
rewrite big_undup; apply/eq_bigr=> x _ /=.
by rewrite intmulpE ?count_ge0 ZM.AddMonoid.iteropE.
qed.
end BigZModule.

(* -------------------------------------------------------------------- *)
abstract theory BigComRing.
type t.

clone import Ring.ComRing as CR with type t <- t.
clear [CR.* CR.AddMonoid.* CR.MulMonoid.*].

(* -------------------------------------------------------------------- *)
theory BAdd.
clone include BigZModule with
  type t <- t,
    op ZM.zeror  <- CR.zeror,
    op ZM.( + )  <- CR.( + ),
    op ZM.([-])  <- CR.([-]),
    op ZM.intmul <- CR.intmul

  proof ZM.* remove abbrev ZM.(-).

realize ZM.addrA. by apply/addrA. qed.
realize ZM.addrC. by apply/addrC. qed.
realize ZM.add0r. by apply/add0r. qed.
realize ZM.addNr. by apply/addNr. qed.

lemma nosmt sumr_1 (P : 'a -> bool) s:
  big P (fun i => oner) s = CR.ofint (count P s).
proof. by apply/sumr_const. qed.

lemma mulr_suml (P : 'a -> bool) F s x :
  (big P F s) * x = big P (fun i => F i * x) s.
proof. by rewrite big_distrl //; (apply/mul0r || apply/mulrDl). qed.

lemma mulr_sumr (P : 'a -> bool) F s x :
  x * (big P F s) = big P (fun i => x * F i) s.
proof. by rewrite big_distrr //; (apply/mulr0 || apply/mulrDr). qed.

lemma divr_suml (P : 'a -> bool) F s x :
  (big P F s) / x = big P (fun i => F i / x) s.
proof. by rewrite mulr_suml; apply/eq_bigr. qed.

lemma nosmt sum_pair_dep ['a 'b] u v J : uniq J =>
    big predT (fun (ij : 'a * 'b) => (u ij.`1 * v ij.`1 ij.`2)%CR) J
  = big predT
      (fun i => u i * big predT
         (fun ij : _ * _ => v ij.`1 ij.`2)
         (filter (fun ij : _ * _ => ij.`1 = i) J))
      (undup (unzip1 J)).
proof.
move=> uqJ; rewrite big_pair // &(eq_bigr) => /= a _.
by rewrite mulr_sumr !big_filter &(eq_bigr) => -[a' b] /= ->>.
qed.

lemma nosmt sum_pair ['a 'b] u v J : uniq J =>
    big predT (fun (ij : 'a * 'b) => (u ij.`1 * v ij.`2)%CR) J
  = big predT
      (fun i => u i * big predT v (unzip2 (filter (fun ij : _ * _ => ij.`1 = i) J)))
      (undup (unzip1 J)).
proof.
move=> uqJ; rewrite (@sum_pair_dep u (fun _ => v)) // &(eq_bigr) /=.
by move=> a _ /=; congr; rewrite big_map predT_comp /(\o).
qed.
end BAdd.

(* -------------------------------------------------------------------- *)
theory BMul.
clone include Bigop with
  type t <- t,
  op   Support.idm <- CR.oner,
  op   Support.(+) <- CR.( * )

  proof Support.*.

realize Support.Axioms.addmA. by apply/mulrA. qed.
realize Support.Axioms.addmC. by apply/mulrC. qed.
realize Support.Axioms.add0m. by apply/mul1r. qed.
end BMul.

(* -------------------------------------------------------------------- *)
lemma mulr_big (P Q : 'a -> bool) (f g : 'a -> t) r s:
    BAdd.big P f r * BAdd.big Q g s
  = BAdd.big P (fun x => BAdd.big Q (fun y => f x * g y) s) r.
proof.
elim: r s => [|x r ih] s; first by rewrite BAdd.big_nil mul0r.
rewrite !BAdd.big_cons; case: (P x) => Px; last by rewrite ih.
by rewrite mulrDl -ih BAdd.mulr_sumr.
qed.
end BigComRing.

(* -------------------------------------------------------------------- *)
abstract theory BigOrder.
type t.

clone import Number.RealDomain as Num with type t <- t.
clear [Num.*].

import Num.Domain.

clone include BigComRing with
  type t <- t,
  pred CR.unit   <- Num.Domain.unit,
    op CR.zeror  <- Num.Domain.zeror,
    op CR.oner   <- Num.Domain.oner,
    op CR.( + )  <- Num.Domain.( + ),
    op CR.([-])  <- Num.Domain.([-]),
    op CR.( * )  <- Num.Domain.( * ),
    op CR.invr   <- Num.Domain.invr,
    op CR.intmul <- Num.Domain.intmul,
    op CR.ofint  <- Num.Domain.ofint,
    op CR.exp    <- Num.Domain.exp

    proof * remove abbrev CR.(-) remove abbrev CR.(/).

realize CR.addrA     . proof. by apply/Num.Domain.addrA. qed.
realize CR.addrC     . proof. by apply/Num.Domain.addrC. qed.
realize CR.add0r     . proof. by apply/Num.Domain.add0r. qed.
realize CR.addNr     . proof. by apply/Num.Domain.addNr. qed.
realize CR.oner_neq0 . proof. by apply/Num.Domain.oner_neq0. qed.
realize CR.mulrA     . proof. by apply/Num.Domain.mulrA. qed.
realize CR.mulrC     . proof. by apply/Num.Domain.mulrC. qed.
realize CR.mul1r     . proof. by apply/Num.Domain.mul1r. qed.
realize CR.mulrDl    . proof. by apply/Num.Domain.mulrDl. qed.
realize CR.mulVr     . proof. by apply/Num.Domain.mulVr. qed.
realize CR.unitP     . proof. by apply/Num.Domain.unitP. qed.
realize CR.unitout   . proof. by apply/Num.Domain.unitout. qed.

lemma nosmt ler_sum (P : 'a -> bool) (F1 F2 :'a -> t) s:
     (forall a, P a => F1 a <= F2 a)
  => (BAdd.big P F1 s <= BAdd.big P F2 s).
proof.
apply: (@BAdd.big_ind2 (fun (x y : t) => x <= y)) => //=.
  by apply/ler_add.
qed.

lemma nosmt sumr_ge0 (P : 'a -> bool) (F : 'a -> t) s:
     (forall a, P a => zeror <= F a)
  => zeror <= BAdd.big P F s.
proof.
move=> h; apply: (@BAdd.big_ind (fun x => zeror <= x)) => //=.
  by apply/addr_ge0.
qed.

lemma sumr_norm P F s :
  (forall x, P x => zeror <= F x) =>
    BAdd.big<:'a> P (fun x => `|F x|) s = BAdd.big P F s.
proof.
by move=> ge0_F; apply: BAdd.eq_bigr => /= a Pa; rewrite ger0_norm /#.
qed.

lemma nosmt prodr_ge0 (P : 'a -> bool) F s:
     (forall a, P a => zeror <= F a)
  => zeror <= BMul.big P F s.
proof.
move=> h; apply: (@BMul.big_ind (fun x => zeror <= x)) => //=.
  by apply/mulr_ge0.
qed.

lemma nosmt prodr_gt0 (P : 'a -> bool) F s:
     (forall a, P a => zeror < F a)
  => zeror < BMul.big P F s.
proof.
move=> h; apply: (@BMul.big_ind (fun x => zeror < x)) => //=.
  by apply/mulr_gt0.
qed.

lemma nosmt ler_prod (P : 'a -> bool) (F1 F2 :'a -> t) s:
     (forall a, P a => zeror <= F1 a <= F2 a)
  => (BMul.big P F1 s <= BMul.big P F2 s).
proof.
move=> h; elim: s => [|x s ih]; first by rewrite !BMul.big_nil lerr.
rewrite !BMul.big_cons; case: (P x)=> // /h [ge0F1x leF12x].
by apply/ler_pmul=> //; apply/prodr_ge0=> a /h [].
qed.

lemma nosmt ler_sum_seq (P : 'a -> bool) (F1 F2 :'a -> t) s:
     (forall a, mem s a => P a => F1 a <= F2 a)
  => (BAdd.big P F1 s <= BAdd.big P F2 s).
proof.
move=> h; rewrite !(@BAdd.big_seq_cond P).
by rewrite ler_sum=> //= x []; apply/h.
qed.

lemma nosmt sumr_ge0_seq (P : 'a -> bool) (F : 'a -> t) s:
     (forall a, mem s a => P a => zeror <= F a)
  => zeror <= BAdd.big P F s.
proof.
move=> h; rewrite !(@BAdd.big_seq_cond P).
by rewrite sumr_ge0=> //= x []; apply/h.
qed.

lemma nosmt prodr_ge0_seq (P : 'a -> bool) F s:
     (forall a, mem s a => P a => zeror <= F a)
  => zeror <= BMul.big P F s.
proof.
move=> h; rewrite !(@BMul.big_seq_cond P).
by rewrite prodr_ge0=> //= x []; apply/h.
qed.

lemma nosmt prodr_gt0_seq (P : 'a -> bool) F s:
     (forall a, mem s a => P a => zeror < F a)
  => zeror < BMul.big P F s.
proof.
move=> h; rewrite !(@BMul.big_seq_cond P).
by rewrite prodr_gt0=> //= x []; apply/h.
qed.

lemma nosmt ler_prod_seq (P : 'a -> bool) (F1 F2 : 'a -> t) s:
     (forall a, mem s a => P a => zeror <= F1 a <= F2 a)
  => (BMul.big P F1 s <= BMul.big P F2 s).
proof.
move=> h; rewrite !(@BMul.big_seq_cond P).
by rewrite ler_prod=> //= x []; apply/h.
qed.

lemma nosmt prodr_eq0 P F s:
      (exists x, P x /\ x \in s /\ F x = zeror)
  <=> BMul.big<:'a> P F s = zeror.
proof. split.
+ case=> x [# Px x_in_s z_Fx]; rewrite (@BMul.big_rem _ _ _ x) //.
  by rewrite Px /= z_Fx Num.Domain.mul0r.
+ elim: s => [|x s ih] /=; 1: by rewrite BMul.big_nil oner_neq0.
  rewrite BMul.big_cons /=; case: (P x) => Px; last first.
  - by move/ih; case=> y [# Py ys z_Fy]; exists y; rewrite Py ys z_Fy.
  rewrite mulf_eq0; case=> [z_Fx|]; first by exists x.
  by move/ih; case=> y [# Py ys z_Fy]; exists y; rewrite Py ys z_Fy.
qed.

lemma nosmt mulr_const s c:
  BMul.big<:'a> predT (fun _ => c) s = exp c (size s).
proof.
rewrite BMul.big_const -MulMonoid.iteropE /exp.
by rewrite IntOrder.ltrNge size_ge0 /= count_predT.
qed.
end BigOrder.
