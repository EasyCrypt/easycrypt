(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Bool AllCore IntDiv List Ring StdRing StdOrder StdBigop.
require (*--*) FinType Word.
(*---*) import IntID IntOrder Bigint Bigint.BIA.

pragma +implicits.

(* -------------------------------------------------------------------- *)
theory BS2Int.

op bs2int (s : bool list) =
  BIA.bigi predT (fun i => 2^i * b2i (nth false s i)) 0 (size s).

op int2bs (N n : int) =
  mkseq (fun i => (n %/ 2^i) %% 2 <> 0) N.

lemma size_int2bs N n : size (int2bs N n) = max 0 N.
proof. by apply/size_mkseq. qed.

lemma bs2int_nil : bs2int [] = 0.
proof. by rewrite /bs2int BIA.big_geq. qed.

lemma bs2int_cons x s :
  bs2int (x :: s) = b2i x + 2 * bs2int s.
proof.
  rewrite /bs2int /= (addrC 1) Bigint.BIA.big_int_recl ?size_ge0 /= expr0 /=.
  congr => //; rewrite Bigint.BIA.mulr_sumr; apply Bigint.BIA.eq_big_seq.
  move => K /= HK_range; rewrite (@eqz_leq _ 0) -ltzE ltzNge.
  move/mem_range: (HK_range) => [-> _] /=.
  by rewrite mulrA exprS //; move/mem_range: HK_range.
qed.

lemma bs2int_nseq_false N :
  bs2int (nseq N false) = 0.
proof.
  case (0 <= N) => [le0N|/ltzNge/ltzW leN0]; last by rewrite nseq0_le // bs2int_nil.
  elim N le0N => /=; rewrite ?nseq0 ?bs2int_nil // => N le0N.
  by rewrite nseqS // bs2int_cons /b2i => ->.
qed.

lemma nosmt bs2int_rcons b (s : bool list):
  bs2int (rcons s b) = (bs2int s) + 2^(size s) * (b2i b).
proof.
rewrite /bs2int size_rcons BIA.big_int_recr ?size_ge0 //=.
rewrite nth_rcons (@ltrr (size s)) /=; congr.
by apply/BIA.eq_big_int=> i [_ lt_is] /=; rewrite nth_rcons lt_is.
qed.

lemma int2bs0s i : int2bs 0 i = [].
proof. by apply/mkseq0. qed.

lemma int2bs0s_le N i : N <= 0 => int2bs N i = [].
proof. by apply/mkseq0_le. qed.

lemma int2bs0 N : int2bs N 0 = nseq N false.
proof.
apply/(eq_from_nth false); rewrite size_int2bs ?size_nseq //.
case: (N <= 0) => [le0_N i|]; 1: by rewrite ler_maxl ?ler_lt_asym.
move/ltrNge => @/max ^gt0_N ->/= i lt_in.
by rewrite nth_nseq ?nth_mkseq //= div0z mod0z.
qed.

lemma int2bs_nseq_false N n :
  (2 ^ N) %| n =>
  int2bs N n = nseq N false.
proof.
  move => /dvdzP [q ->>]; rewrite /int2bs -mkseq_nseq.
  apply eq_in_mkseq => K /mem_range HK_range /=.
  apply negeqF => /=; rewrite -IntDiv.divzpMr.
  + by apply dvdz_exp2l; move/mem_range: HK_range => [-> /ltzW].
  rewrite -IntDiv.exprD_subz //; first by move/mem_range: HK_range => [-> /ltzW].
  rewrite -dvdzE dvdz_mull; move: (dvdz_exp2l 2 1 (N - K)); rewrite expr1 /= => -> //.
  by apply/ltzS/ltr_subl_addr/ltr_subr_addr; move/mem_range: HK_range.
qed.

lemma nosmt int2bsS N i : 0 <= N =>
  int2bs (N + 1) i = rcons (int2bs N i) ((i %/ 2^N) %% 2 <> 0).
proof. by apply/mkseqS. qed.

lemma int2bs_cons N n :
  0 < N =>
  int2bs N n = (!2 %| n) :: int2bs (N - 1) (n %/ 2).
proof.
  move => lt0N; rewrite /int2bs; move: (subrK N 1) => {1}<-; rewrite mkseqSr /=; first by apply/subr_ge0; move/ltzE: lt0N.
  rewrite expr0 dvdzE /=; apply eq_in_mkseq => K [le0K _]; rewrite /(\o) /=.
  by rewrite -divz_mul // -exprS // (addrC 1).
qed.

lemma int2bs_mod N n :
  int2bs N (n %% 2 ^ N) = int2bs N n.
proof.
  apply eq_in_mkseq => K /mem_range HK_range /=.
  rewrite IntDiv.modz_pow2_div; first by move/mem_range: HK_range => [-> /=]; apply ltzW.
  rewrite modz_dvd //; move: (dvdz_exp2l 2 1 (N - K)); rewrite expr1 => /= -> //.
  by apply/ler_subr_addl/ltzE; move/mem_range: HK_range.
qed.

lemma nosmt bs2int_eq N i j: 0 <= i => 0 <= j => i %% 2^N = j %% 2^N =>
  int2bs N i = int2bs N j.
proof.
move=> ge0_i ge0_j eq; apply/eq_in_mkseq=> k [ge0_k lt_kN] /=.
move/(congr1 (fun z => z %/ 2^k)): eq => /=.
have ge0_N: 0 <= N by apply/(ler_trans _ ge0_k)/ltrW.
rewrite !modz_pow2_div // ?ge0_k ?ltrW //.
move/(congr1 (fun z => z %% 2^1))=> /=; rewrite !modz_dvd_pow /=;
  first 2 by (rewrite ler_subr_addr lez_add1r).
by rewrite !expr1 => ->.
qed.

lemma bs2int_ge0 s : 0 <= bs2int s.
proof.
elim/last_ind: s => /= [|s b ih]; 1: by rewrite bs2int_nil.
by rewrite bs2int_rcons addr_ge0 ?ih mulr_ge0 ?b2i_ge0 ltrW expr_gt0.
qed.

lemma bs2int_le2Xs s : bs2int s < 2^(size s).
proof.
elim/last_ind: s=> /= [|s b ih]; first by rewrite bs2int_nil expr0.
rewrite bs2int_rcons size_rcons exprS ?size_ge0.
(have {2}->: 2=1+1 by done); rewrite mulrDl mul1r ltr_le_add //.
by rewrite ler_pimulr ?b2i_le1 ltrW expr_gt0.
qed.

(* -------------------------------------------------------------------- *)
lemma bs2intK s : int2bs (size s) (bs2int s) = s.
proof.
elim/last_ind: s=> /= [|s b ih]; 1: by rewrite bs2int_nil int2bs0s.
rewrite bs2int_rcons size_rcons int2bsS ?size_ge0.
rewrite -(@int2bs_mod (size s)).
rewrite mulrC modzMDr int2bs_mod; congr.
have gt0_2Xs: 0 < 2  ^ (size s) by rewrite expr_gt0.
rewrite divzMDr 1:gtr_eqF // divz_small /=.
  by rewrite bs2int_ge0 gtr0_norm ?bs2int_le2Xs.
by rewrite mod2_b2i b2i_eq0.
qed.

(* -------------------------------------------------------------------- *)
lemma int2bsK N i : 0 <= N => 0 <= i < 2^N => bs2int (int2bs N i) = i.
proof.
move=> ge0N; elim: N ge0N i=> /= [|n ge0_n ih] i.
  rewrite expr0 ltz1 -eqr_le => <-; rewrite int2bs0.
  by rewrite nseq0_le // bs2int_nil.
case=> [ge0_i lt_i2XSn]; rewrite int2bsS // bs2int_rcons.
rewrite -{1}int2bs_mod // ih //=.
  by rewrite modz_ge0 ?gtr_eqF ?ltz_pmod ?expr_gt0.
rewrite size_int2bs ler_maxr // eq_sym {1}(@divz_eq i (2^n)).
rewrite addrC mulrC; do 2! congr; move: lt_i2XSn.
rewrite exprS // -ltz_divLR ?expr_gt0 // => lt.
rewrite -{1}(@modz_small (i %/ 2^n) 2) ?ger0_norm ?b2i_mod2 //.
by rewrite lt /= divz_ge0 ?expr_gt0.
qed.

(* -------------------------------------------------------------------- *)
lemma int2bs_cat K N n :
  0 <= K <= N =>
  int2bs N n = (int2bs K n) ++ (int2bs (N - K) (n %/ (2 ^ K))).
proof.
  move => [le0K leKN]; rewrite /int2bs.
  (*FIXME: why does it not work? Pierre-Yves*)
  (*rewrite -{1}(subrK N K) (addrC _ K).*)
  move: (subrK N K) => {1}<-.
  move: (addrC (N - K) K) => ->.
  rewrite mkseq_add ?subr_ge0 //.
  congr; apply eq_in_mkseq => I /= [le0I _].
  by rewrite exprD_nneg // IntDiv.divz_mul // expr_ge0.
qed.

lemma int2bs1 N :
  0 < N =>
  int2bs N 1 = true :: nseq (N - 1) false.
proof. by move => lt0N; rewrite int2bs_cons // dvdzE /= int2bs_nseq_false. qed.

lemma int2bs_mulr_pow2 K N n :
  0 <= K <= N =>
  int2bs N (2 ^ K * n) = nseq K false ++ int2bs (N - K) n.
proof.
  move => [le0K leKN]; rewrite /int2bs.
  (*FIXME: same.*)
  (*rewrite -{1}(subrK N K) (addrC _ K).*)
  move: (subrK N K) => {1}<-.
  move: (addrC (N - K) K) => ->.
  rewrite mkseq_add //; first by apply/subr_ge0.
  rewrite -/int2bs.
  (*FIXME: same.*)
  (*rewrite -(int2bs_nseq_false _ (2 ^ K * n)).*)
  move: (int2bs_nseq_false K (2 ^ K * n)) => <-.
  + by apply/dvdz_mulr/dvdzz.
  congr => //; apply eq_in_mkseq => I /= /mem_range HI_range.
  rewrite exprD_nneg //; first by move/mem_range: HI_range.
  by rewrite divzMpl //; apply expr_gt0.
qed.

lemma int2bs_divr_pow2 K N n :
  int2bs N (n %/ 2 ^ K) = drop `|K| (int2bs (N + `|K|) n).
proof.
  rewrite pow_normr; case (0 <= N) => [le0N|/ltzNge/ltzW leN0]; last first.
  + by rewrite drop_oversize; [rewrite size_int2bs ler_maxrP normr_ge0 ler_naddl|rewrite int2bs0s_le].
  (*FIXME: same.*)
  (*rewrite (int2bs_cat `|K| (N + `|K|)) ?normr_ge0 ?lez_addr //= drop_size_cat -?addrA //=.*)
  move: (int2bs_cat `|K| (N + `|K|)) => ->; rewrite ?normr_ge0 ?lez_addr //= drop_size_cat -?addrA //=.
  by rewrite size_int2bs ler_maxr // normr_ge0.
qed.

lemma int2bs_pow2 K N :
  K \in range 0 N =>
  int2bs N (2 ^ K) = nseq K false ++ true :: nseq (N - 1 - K) false.
proof.
  move => HK_range; move: (int2bs_mulr_pow2 K N 1) => /= ->.
  + by split; move/mem_range: HK_range => // [_ ltKN] _; apply ltzW.
  rewrite int2bs1; first by apply subr_gt0; move/mem_range:HK_range.
  by rewrite addrAC.
qed.

(*-----------------------------------------------------------------------------*)
lemma bs2int_cat s1 s2 :
  bs2int (s1 ++ s2) = bs2int s1 + (2 ^ (size s1)) * bs2int s2.
proof.
  elim/last_ind: s2 => [|s2 b]; first by rewrite cats0 bs2int_nil.
  rewrite -rcons_cat !bs2int_rcons mulrDr addrA mulrA size_cat => ->.
  by rewrite exprD_nneg ?size_ge0.
qed.

lemma bs2int_range s :
  bs2int s \in range 0 (2 ^ size s).
proof. by apply/mem_range; split; [apply bs2int_ge0|move => _; apply bs2int_le2Xs]. qed.

lemma bs2int1 N :
  bs2int (true :: nseq N false) = 1.
proof. by rewrite bs2int_cons bs2int_nseq_false /b2i. qed.

lemma bs2int_mulr_pow2 N s :
  bs2int (nseq N false ++ s) = 2 ^ max 0 N * bs2int s.
proof. by rewrite bs2int_cat bs2int_nseq_false size_nseq. qed.

lemma bs2int_pow2 K N :
  bs2int (nseq K false ++ true :: nseq N false) = 2 ^ max 0 K.
proof. by rewrite bs2int_mulr_pow2 bs2int1. qed.

end BS2Int.


(* -------------------------------------------------------------------- *)
theory BitReverse.

import BS2Int.

op bitrev N n = bs2int (rev (int2bs N n)).

lemma bitrev_neg N n :
  N <= 0 =>
  bitrev N n = 0.
proof. by rewrite /bitrev => leN0; move: (size_int2bs N n); rewrite ler_maxl // size_eq0 => ->; rewrite rev_nil bs2int_nil. qed.

lemma bitrev_cons N n :
  0 < N =>
  bitrev N n = 2 ^ (N - 1) * b2i (!2 %| n) + bitrev (N - 1) (n %/ 2).
proof.
  move => lt0N; rewrite /bitrev int2bs_cons // rev_cons -cats1 bs2int_cat size_rev size_int2bs ler_maxr; first by rewrite -ltzS.
  by rewrite bs2int_cons; move: (bs2int_nseq_false 0); rewrite nseq0 => -> /=; rewrite addrC.
qed.

(*hint simplify bitrev_neg, bitrev_cons.*)

lemma bitrev_ge0 N n :
  0 <= bitrev N n.
proof. by rewrite /bitrev bs2int_ge0. qed.

(*TODO: weird name.*)
print bs2int_le2Xs.
lemma bitrev_lt_pow2 N n :
  bitrev N n < 2 ^ N.
proof.
  case (0 <= N) => [le0N|/ltrNge /ltzW leN0]; last by rewrite bitrev_neg // expr_gt0.
  rewrite /bitrev; move: (bs2int_le2Xs (rev (int2bs N n))).
  by rewrite size_rev size_int2bs ler_maxr.
qed.

lemma bitrev_range N n :
  bitrev N n \in range 0 (2 ^ N).
proof. by rewrite mem_range bitrev_ge0 bitrev_lt_pow2. qed.

lemma bitrev_cat K N n :
  0 <= K <= N =>
  bitrev N n = bitrev (N - K) (n %/ 2 ^ K) + 2 ^ (N - K) * bitrev K n.
proof. by move => [le0K leKN]; rewrite /bitrev (int2bs_cat K) // rev_cat bs2int_cat size_rev size_int2bs ler_maxr // subr_ge0. qed.

lemma bitrev_mod N n :
  bitrev N (n %% 2 ^ N) = bitrev N n.
proof. by rewrite /bitrev int2bs_mod. qed.

lemma bitrev_involutive N n :
  0 <= N =>
  n \in range 0 (2 ^ N) =>
  bitrev N (bitrev N n) = n.
proof.
  move => le0N Hn_range; rewrite /bitrev.
  move: (bs2intK (rev (int2bs N n))).
  rewrite size_rev size_int2bs ler_maxr // => ->.
  by rewrite revK int2bsK // -mem_range.
qed.

lemma bitrev_injective N n1 n2 :
  0 <= N =>
  n1 \in range 0 (2 ^ N) =>
  n2 \in range 0 (2 ^ N) =>
  bitrev N n1 = bitrev N n2 =>
  n1 = n2.
proof. by move => le0N Hn1_range Hn2_range eq_bitrev; rewrite -(bitrev_involutive N n1) // -(bitrev_involutive N n2) // eq_bitrev. qed.

lemma bitrev_bijective N n1 n2 :
  0 <= N =>
  n1 \in range 0 (2 ^ N) =>
  n2 \in range 0 (2 ^ N) =>
  bitrev N n1 = bitrev N n2 <=>
  n1 = n2.
proof. by move => le0n Hn1_range Hn2_range; split => [|-> //]; apply bitrev_injective. qed.

lemma bitrev0 N :
  bitrev N 0 = 0.
proof. by rewrite /bitrev int2bs0 rev_nseq bs2int_nseq_false. qed.

lemma bitrev1 N :
  0 < N =>
  bitrev N 1 = 2 ^ (N - 1).
proof.
  move => lt0N; rewrite /bitrev int2bs1 // rev_cons bs2int_rcons rev_nseq.
  by rewrite size_nseq bs2int_nseq_false /b2i /= ler_maxr // subr_ge0; move/ltzE: lt0N.
qed.

lemma bitrev_mulr_pow2 K N n :
  0 <= K <= N =>
  bitrev N (2 ^ K * n) = bitrev N n %/ 2 ^ K.
proof.
  move => [le0K leKN]; rewrite /bitrev int2bs_mulr_pow2 // rev_cat rev_nseq bs2int_cat bs2int_nseq_false /=.
  rewrite (int2bs_cat (N - K) N); first by split; [rewrite subr_ge0|move => _; rewrite ler_subl_addr ler_addl].
  rewrite rev_cat bs2int_cat size_rev size_int2bs opprD addrA /= ler_maxr // (mulrC (exp _ _)%IntDiv) divzMDr.
  + by apply/gtr_eqF/expr_gt0.
  by rewrite divz_small // -mem_range normrX_nat // bitrev_range.
qed.

lemma bitrev_divr_pow2 K N n :
  0 <= K <= N =>
  bitrev N (n %/ 2 ^ K) = (bitrev (N + K) n) %% (2 ^ N).
proof.
  move => [le0K leKN]; rewrite /bitrev int2bs_divr_pow2 ger0_norm // /int2bs drop_mkseq.
  + by split => // _; rewrite ler_addr (lez_trans K).
  rewrite -addrA /= addrC mkseq_add //; first by apply/(lez_trans K).
  rewrite rev_cat bs2int_cat size_rev size_mkseq ler_maxr //; first by apply/(lez_trans K).
  rewrite mulrC modzMDr modz_small //.
  rewrite -mem_range normrX_nat; first by apply/(lez_trans K).
  move: (bs2int_range (rev (mkseq (fun (i : int) => (fun (i0 : int) => n %/ 2 ^ i0 %% 2 <> 0) (K + i)) N))).
  by rewrite size_rev size_mkseq ler_maxr //; apply/(lez_trans K).
qed.

lemma bitrev_pow2 K N :
  K \in range 0 N =>
  bitrev N (2 ^ K) = 2 ^ (N - 1 - K).
proof.
  move => HK_range; move: (bitrev_mulr_pow2 K N 1) => /= ->; first by rewrite (ltzW K); move/mem_range: HK_range.
  rewrite bitrev1; first by apply/(ler_lt_trans K); move/mem_range: HK_range.
  by rewrite -exprD_subz //= -(ltzS K); move/mem_range: HK_range.
qed.

lemma bitrev_range_dvdz K N n :
  0 <= K <= N =>
  n \in range 0 (2 ^ (N - K)) =>
  2 ^ K %| bitrev N n.
proof.
  move => [le0K leKN] Hn_range; rewrite (bitrev_cat (N - K)) //.
  + by rewrite subr_ge0 leKN /= ler_subl_addl -ler_subl_addr.
  rewrite opprD addrA /= divz_small; first by rewrite -mem_range normrX_nat // subr_ge0.
  by rewrite bitrev0 /= dvdz_mulr dvdzz.
qed.

lemma bitrev_dvdz_range K N n :
  0 <= K <= N =>
  (2 ^ (N - K)) %| n =>
  bitrev N n \in range 0 (2 ^ K).
proof.
  move => [le0K leKN] dvdz_n; rewrite (bitrev_cat (N - K)).
  + by rewrite subr_ge0 leKN /= ler_subl_addl -ler_subl_addr.
  rewrite opprD addrA /=; move/dvdzP: dvdz_n => [q ->>].
  rewrite (mulrC q) bitrev_mulr_pow2.
  + by rewrite subr_ge0 leKN.
  rewrite (divz_small (bitrev _ _)) /=; last by apply bitrev_range.
  by rewrite -mem_range normrX_nat ?subr_ge0 // bitrev_range.
qed.

lemma bitrev_add K N m n :
  0 <= K <= N =>
  m \in range 0 (2 ^ K) =>
  bitrev N (m + 2 ^ K * n) = bitrev N m + bitrev N n %/ 2 ^ K.
proof.
  move => [le0K leKN] Hm_range; rewrite (bitrev_cat K) //.
  rewrite (mulrC (exp _ _)) divzMDr; first by apply/gtr_eqF/expr_gt0.
  rewrite divz_small /=; first by rewrite -mem_range normrX_nat.
  rewrite -(bitrev_mod K) modzMDr bitrev_mod (addrC (bitrev _ _)); congr.
  + rewrite (bitrev_cat K N) // divz_small; last by rewrite bitrev0.
    by rewrite -mem_range normrX_nat.
  rewrite (bitrev_cat (N - K) N).
  + by split; [rewrite subr_ge0|move => _; rewrite ler_subl_addr ler_addl].
  rewrite !opprD addrA /= (mulrC (exp _ _)) divzMDr.
  + by apply/gtr_eqF/expr_gt0.
  by rewrite divz_small // -mem_range normrX_nat // bitrev_range.
qed.

lemma bitrev2_le M N n :
  0 <= M <= N =>
  bitrev M (bitrev N n) = n %% 2 ^ N %/ 2 ^ (N - M).
proof.
  move => [le0M leMN]; rewrite -(bitrev_mod N) /bitrev (int2bs_cat (N - M) N).
  + by rewrite subr_ge0 ler_subl_addl -ler_subl_addr.
  rewrite opprD addrA /= rev_cat bs2int_cat size_rev size_int2bs ler_maxr //.
  rewrite -{1}int2bs_mod mulrC modzMDr int2bs_mod.
  move: (bitrev_involutive M (n %% 2 ^ N %/ 2 ^ (N - M)) _ _) => //.
  rewrite range_div_range /=; first by apply/expr_gt0.
  rewrite -exprD_nneg //; first by apply/subr_ge0.
  rewrite addrA addrAC /=; move: (mem_range_mod n (2 ^ N)).
  by rewrite normrX_nat; [apply/(lez_trans M)|move => -> //; apply/gtr_eqF/expr_gt0].
qed.

lemma bitrev2_ge M N n :
  0 <= N <= M =>
  bitrev M (bitrev N n) = 2 ^ (M - N) * (n %% 2 ^ N).
proof.
  move => [le0N leNM]; rewrite -(bitrev_mod N) /bitrev (int2bs_cat N M) //.
  rewrite divz_small; first by rewrite -mem_range normrX_nat // bitrev_range.
  rewrite int2bs0 rev_cat rev_nseq bs2int_cat size_nseq ler_maxr ?subr_ge0 //.
  rewrite bs2int_nseq_false /=; congr; move: (bitrev_involutive N (n %% 2 ^ N) _ _) => //.
  by move: (mem_range_mod n (2 ^ N)); rewrite normrX_nat; [apply/(lez_trans N)|move => -> //; apply/gtr_eqF/expr_gt0].
qed.

lemma bitrev_range_pow2_perm_eq K N :
  0 <= K <= N =>
  perm_eq
    (map (bitrev N)            (range 0 (2 ^ K)))
    (map (( * ) (2 ^ (N - K))) (range 0 (2 ^ K))).
proof.
  move => [le0K leKN]; rewrite perm_eqP_pred1 => x.
  rewrite !count_uniq_mem.
  + rewrite map_inj_in_uniq ?range_uniq // => {x} x y Hx_range Hy_range.
    apply/bitrev_injective; first last.
    - by move: Hx_range; apply/mem_range_incl => //; apply/ler_weexpn2l.
    - by move: Hy_range; apply/mem_range_incl => //; apply/ler_weexpn2l.
    by apply/(lez_trans K).
  + rewrite map_inj_in_uniq ?range_uniq // => {x} x y Hx_range Hy_range.
    by apply/mulfI/gtr_eqF/expr_gt0.
  congr; rewrite eq_iff !mapP; split => -[y [Hy_range ->>]].
  + exists (bitrev N y %/ (2 ^ (N - K))).
    rewrite mulrC divzK /=.
    - apply/bitrev_range_dvdz; last by rewrite opprD addrA.
      by rewrite subr_ge0 leKN /= ger_addl oppz_le0.
    rewrite range_div_range ?expr_gt0 //= -exprD_nneg ?subr_ge0 //.
    by rewrite addrA addrAC /= bitrev_range.
  exists (bitrev N y %/ (2 ^ (N - K))).
  rewrite -bitrev_mulr_pow2 ?bitrev_involutive /=.
  + by rewrite subr_ge0 leKN /= ger_addl oppz_le0.
  + by apply/(lez_trans K).
  + rewrite mem_range_mull ?expr_gt0 //=.
    rewrite -(mulN1r (exp _ _)%Int) -divzpMr.
    - by rewrite dvdz_exp2l subr_ge0 leKN /= ger_addl oppz_le0.
    rewrite mulN1r opprK -exprD_subz // ?opprD ?addrA //=.
    by rewrite subr_ge0 leKN /= ger_addl oppz_le0.
  by rewrite bitrev_dvdz_range // dvdz_mulr dvdzz.
qed.

lemma bitrev_mul_range_pow2_perm_eq K M N :
  0 <= K =>
  0 <= M =>
  K + M <= N =>
  perm_eq
    (map (bitrev N \o (( * ) (2 ^ M))) (range 0 (2 ^ K)))
    (map (( * ) (2 ^ (N - K - M)))     (range 0 (2 ^ K))).
proof.
  move => le0K le0M le_N.
  move: (eq_in_map (bitrev N \o ( * ) (2 ^ M)) (transpose (%/) (2 ^ M) \o (bitrev N)) (range 0 (2 ^ K))).
  move => [Heq_map _]; move: Heq_map => -> => [x Hx_range|]; last rewrite map_comp.
  + by rewrite /(\o) bitrev_mulr_pow2; first rewrite le0M /= (lez_trans (K + M)) // ler_addr.
  move: (eq_in_map (( * ) (2 ^ (N - K - M))) ((transpose (fun (m d : int) => m %/ d) (2 ^ M)) \o (( * ) (2 ^ (N - K)))) (range 0 (2 ^ K))).
  move => [Heq_map _]; move: Heq_map => -> => [x Hx_range|].
  (*FIXME*)
  + admit.
  rewrite (map_comp (transpose _ _) (( * )%Int _)) perm_eq_map bitrev_range_pow2_perm_eq.
  by rewrite le0K /= (lez_trans (K + M)) // ler_addl.
qed.

end BitReverse.


(* -------------------------------------------------------------------- *)
theory BitChunking.
op chunk r (bs : 'a list) =
  mkseq (fun i => take r (drop (r * i)%Int bs)) (size bs %/ r).

lemma nosmt chunk_le0 r (s : 'a list) : r <= 0 => chunk r s = [].
proof.
move/ler_eqVlt=> [->|gt0_r] @/chunk; 1: by rewrite mkseq0.
rewrite /chunk mkseq0_le // -oppr_ge0 -divzN.
by rewrite divz_ge0 ?size_ge0 oppr_gt0.
qed.

lemma nosmt nth_flatten x0 n (bs : 'a list list) i :
     all (fun s => size s = n) bs
  => nth x0 (flatten bs) i = nth x0 (nth [] bs (i %/ n)) (i %% n).
proof.
case: (n <= 0) => [ge0_n|/ltrNge gt0_n] /allP /= eqz.
  have bsE: bs = nseq (size bs) [].
    elim: bs eqz => /= [|b bs ih eqz]; 1: by rewrite nseq0.
    rewrite addrC nseqS ?size_ge0 -ih /=.
      by move=> x bsx; apply/eqz; rewrite bsx.
    by rewrite -size_eq0 -leqn0 ?size_ge0 eqz.
  rewrite {2}bsE nth_nseq_if if_same /=.
  rewrite bsE; elim/natind: (size bs)=> [m le0_m|m ge0_m ih];
    by rewrite ?nseqS // nseq0_le // flatten_nil.
case: (i < 0)=> [lt0_i|/lerNgt ge0_i].
  rewrite nth_neg // (@nth_neg []) // ltrNge.
  by rewrite divz_ge0 // -ltrNge.
elim: bs i ge0_i eqz => [|b bs ih] i ge0_i eqz /=.
  by rewrite flatten_nil.
have /(_ b) /= := eqz; rewrite flatten_cons nth_cat => ->.
have <-: (i < n) <=> (i %/ n = 0) by rewrite -divz_eq0 // ge0_i.
case: (i < n) => [lt_in|/lerNgt le_ni]; 2: rewrite ih ?subr_ge0 //.
+ by rewrite modz_small // ge0_i ltr_normr ?lt_in.
+ by move=> x bx; have := eqz x; apply; rewrite /= bx.
rewrite -mulN1r modzMDr; congr.
case: (n = 0)=> [^zn ->/=|nz_n]; 2: by rewrite divzMDr 1?addrC.
rewrite eq_sym nth_neg ?oppr_lt0 // => {ih}; move: eqz.
by case: bs => // c bs /(_ c) /=; rewrite zn size_eq0 => ->.
qed.

lemma size_chunk r (bs : 'a list) : 0 < r =>
  size (chunk r bs) = size bs %/ r.
proof.
move=> gt0_r; rewrite size_mkseq ler_maxr //.
by rewrite divz_ge0 ?gt0_r ?size_ge0.
qed.

lemma in_chunk_size r (bs : 'a list) b: 0 < r =>
  mem (chunk r bs) b => size b = r.
proof.
move=> gt0_r /mapP [i] [] /mem_iota /= [ge0_i ^lt_is +] ->.
rewrite ltzE -(@ler_pmul2r r) 1:gt0_r divzE mulrDl mul1r.
rewrite -ler_subr_addr addrAC => /ler_trans/(_ (size bs - r) _).
  by rewrite ler_naddr // oppr_le0 modz_ge0 gtr_eqF ?gt0_r.
rewrite (mulrC i) ler_subr_addl -ler_subr_addr => ler.
have ge0_r: 0 <= r by apply/ltrW/gt0_r.
rewrite size_take ?ge0_r size_drop // 1:mulr_ge0 ?ge0_r //.
rewrite ler_maxr 1:subr_ge0 1:-subr_ge0 1:(ler_trans r) ?ge0_r //.
by move/ler_eqVlt: ler=> [<-|->].
qed.

lemma size_flatten_chunk r (bs : 'a list) : 0 < r =>
  size (flatten (chunk r bs)) = (size bs) %/ r * r.
proof.
move=> gt0_r; rewrite size_flatten sumzE big_map.
pose F := fun (x : 'a list) => r; rewrite predT_comp /(\o) /= big_seq.
rewrite (@eq_bigr _ _ F) /F /=; first by move=> i; apply/in_chunk_size.
rewrite -(@big_seq _ (chunk r bs)) big_constz count_predT.
by rewrite size_chunk // mulrC.
qed.

lemma chunkK r (bs : 'a list) : 0 < r =>
  r %| size bs => flatten (chunk r bs) = bs.
proof.
move=> gt0_r dvd_d_bs; apply/(eq_from_nth witness)=> [|i].
  by rewrite size_flatten_chunk // divzK.
rewrite size_flatten_chunk ?divzK // => -[ge0_i lt_ibs].
rewrite (@nth_flatten witness r); 1: apply/allP=> s.
by move/(@in_chunk_size _ _ _ gt0_r).
rewrite nth_mkseq /= 1:divz_ge0 ?ge0_i ?ltz_divRL ?gt0_r //=.
  by apply/(@ler_lt_trans i)=> //; rewrite lez_floor gtr_eqF ?gt0_r.
rewrite nth_take ?ltz_pmod 1:ltrW ?gt0_r nth_drop; last 2 first.
  by rewrite modz_ge0 ?gtr_eqF ?gt0_r. by rewrite (@mulrC r) -divz_eq.
by rewrite mulr_ge0 1:ltrW ?gt0_r // divz_ge0 // gt0_r.
qed.

lemma flattenK r (bs : 'a list list) : 0 < r =>
  (forall b, mem bs b => size b = r) => chunk r (flatten bs) = bs.
proof.
move=> gt0_r; elim: bs => [|x xs ih] h.
  by rewrite flatten_nil /chunk div0z mkseq0.
rewrite flatten_cons /chunk size_cat h // -{3}(mul1r r).
rewrite divzMDl ?gtr_eqF // mkseq_add //=.
  by rewrite divz_ge0 1:gt0_r size_ge0.
rewrite mkseq1 /= drop0 take_cat h //= take0 cats0 /= -{3}ih.
  by move=> b xsb; apply/h; right.
apply/eq_in_mkseq=> i /=; rewrite mulrDr mulr1 drop_cat (@h x) //.
case=> [ge0_i lti]; rewrite ltrNge ler_paddr // 1:mulr_ge0 1:ltrW //.
by rewrite addrAC addrN.
qed.

lemma chunk_cat r (xs ys : 'a list) :
  r %| size xs => chunk r (xs ++ ys) = chunk r xs ++ chunk r ys.
proof.
case: (r <= 0) => [/chunk_le0<:'a> h|/ltrNge lt0_r]; 1: by rewrite !h.
case/dvdzP=> q @/chunk szxs; rewrite size_cat szxs divzMDl ?gtr_eqF //.
rewrite mulzK ?gtr_eqF // mkseq_add ?divz_ge0 ?size_ge0 //=.
  by rewrite -(@ler_pmul2r r) //= -szxs size_ge0.
congr; last first; apply/eq_in_mkseq=> i /=.
  case=> [ge0_i lt_i] /=; rewrite drop_cat szxs (mulrC r) ltr_pmul2r //.
  by rewrite  gtr_addl ltrNge ge0_i /= mulrDl addrAC subrr /= mulrC.
case=> [ge0_i lt_iq]; rewrite drop_cat szxs (mulrC r).
rewrite ltr_pmul2r ?lt_iq //= take_cat; pose s := drop _ _.
suff /ler_eqVlt[->|->//]: r <= size s; 1: rewrite ltrr /=.
  by rewrite take0 take_size cats0.
rewrite size_drop ?mulr_ge0 // 1:ltrW // szxs -mulrBl.
rewrite ler_maxr ?mulr_ge0 1,2:ltrW ?subr_gt0 ?ler_pmull //.
by rewrite ler_subr_addl -ltzE.
qed.
end BitChunking.
