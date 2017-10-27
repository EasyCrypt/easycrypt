(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List.

pred is_finite (p : 'a -> bool) =
  exists s,
       uniq s
    /\ (forall x, mem s x <=> p x).

op to_seq: ('a -> bool) -> 'a list.

axiom to_seq_finite (P : 'a -> bool):
  is_finite P =>
     uniq (to_seq P)
  /\ (forall x, mem (to_seq P) x <=> P x).

lemma uniq_to_seq (P : 'a -> bool):
  is_finite P =>
  uniq (to_seq P).
proof. by move=>/to_seq_finite [-> _]. qed.

lemma mem_to_seq (P : 'a -> bool) x:
  is_finite P =>
  mem (to_seq P) x <=> P x.
proof. by move=>/to_seq_finite [_ ->]. qed.

(* -------------------------------------------------------------------- *)
(* Finite sets can be obtained by union, intersection and difference    *
 * of empty and singleton sets. Finiteness is closed under inclusion.   *)

lemma finite0: is_finite pred0<:'a>.
proof. by exists []. qed.

lemma finite1 (x : 'a): is_finite (pred1 x).
proof. by exists [x]. qed.

lemma finite_leq (B A : 'a -> bool):
  A <= B => is_finite B =>
  is_finite A.
proof.
move=> le_A_B [wB] [uniq_wB wB_univ].
exists (filter A wB); split=> [|x]; first exact/filter_uniq.
by rewrite mem_filter wB_univ; case (A x)=> //=; exact/le_A_B.
qed.

lemma finiteU (A B : 'a -> bool):
  is_finite A => is_finite B =>
  is_finite (predU A B).
proof.
move=> [wA] [uniq_wA wA_univ] [wB] [uniq_wB wB_univ].
exists (undup (wA ++ wB)); split=> [|x]; first by exact/undup_uniq.
by rewrite /predU mem_undup mem_cat wA_univ wB_univ.
qed.

lemma finiteIl (A B : 'a -> bool):
  is_finite A =>
  is_finite (predI A B).
proof.
move=> fin_A; apply/(finite_leq A)=> //=.
exact/predIsubpredl.
qed.

lemma finiteIr (A B : 'a -> bool):
  is_finite B =>
  is_finite (predI A B).
proof.
move=> fin_B; apply/(finite_leq B)=> //=.
exact/predIsubpredr.
qed.

lemma finiteD (A B : 'a -> bool):
  is_finite A =>
  is_finite (predD A B).
proof.
move=> fin_A; apply/(finite_leq A)=> //= x.
by rewrite /predD.
qed.

lemma NfiniteP ['a] n (p : 'a -> bool) : 0 <= n =>
  !is_finite p => exists s, (n <= size s /\ uniq s) /\ (mem s) <= p.
proof.
move=> ge0_n; rewrite /is_finite negb_exists /= => h.
elim: n ge0_n => [|n ge0_n [s [[sz uq_s] ih]]]; first by exists [].
suff [x [px x_notin_s]]: exists x, p x /\ !(x \in s).
+ exists (x :: s); rewrite /= x_notin_s uq_s /= addzC.
  by rewrite lez_add2l sz /= => y; rewrite in_cons => -[->//|/ih].
move: (h s); apply/contraR; rewrite negb_exists uq_s /=.
by move=> + x - /(_ x); rewrite negb_and /= /#.
qed.
