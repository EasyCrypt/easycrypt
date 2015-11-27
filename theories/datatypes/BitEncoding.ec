(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Fun Pred Bool Int IntExtra IntDiv List Ring.
require import StdRing StdOrder StdBigop.
require (*--*) FinType Word.
(*---*) import IntID IntOrder Bigint Bigint.BIA.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op bs2int (s : bool list) =
  BIA.bigi predT (fun i => 2^i * b2i (nth false s i)) 0 (size s).

op int2bs (N n : int) =
  mkseq (fun i => (n %/ 2^i) %% 2 <> 0) N.

lemma size_int2bs N n : size (int2bs N n) = max 0 N.
proof. by apply/size_mkseq. qed.

lemma bs2int_nil : bs2int [] = 0.
proof. by rewrite BIA.big_geq. qed.

lemma bs2int_rcons b (s : bool list):
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
case: (N <= 0) => [le0_N i|]; 1: by rewrite max_lel ?ler_lt_asym.
move/ltrNge => @/max ^gt0_N ->/= i lt_in.
by rewrite nth_nseq ?nth_mkseq //= div0z mod0z.
qed.

lemma int2bsS N i : 0 <= N =>
  int2bs (N + 1) i = rcons (int2bs N i) ((i %/ 2^N) %% 2 <> 0).
proof. by apply/mkseqS. qed.

lemma bs2int_eq N i j: 0 <= i => 0 <= j => i %% 2^N = j %% 2^N =>
  int2bs N i = int2bs N j.
proof.
move=> ge0_i ge0_j eq; apply/eq_in_mkseq=> k [ge0_k lt_kN] /=.
move/(congr1 (fun z => z %/ 2^k)): eq => /=.
have ge0_N: 0 <= N by apply/(ler_trans _ ge0_k)/ltrW.
rewrite !modz_pow2_div // ?ge0_k ?ltrW //.
move/(congr1 (fun z => z %% 2^1))=> /=; rewrite !modz_dvd_pow /=;
  first 2 by (rewrite ler_subr_addr lez_add1r).
by rewrite !pow1 => ->.
qed.

lemma bs2int_mod N i : 0 <= i => int2bs N (i %% 2^N) = int2bs N i.
proof.
move=> ge0_i; apply/bs2int_eq=> //; last by rewrite modz_mod.
by rewrite modz_ge0 // -lt0n ?ltrW // powPos.
qed.

lemma bs2int_ge0 s : 0 <= bs2int s.
proof.
elim/last_ind: s => /= [|s b ih]; 1: by rewrite bs2int_nil.
by rewrite bs2int_rcons addr_ge0 ?ih mulr_ge0 ?b2i_ge0 ltrW powPos.
qed.

lemma bs2int_le2Xs s : bs2int s < 2^(size s).
proof.
elim/last_ind: s=> /= [|s b ih]; first by rewrite bs2int_nil pow0.
rewrite bs2int_rcons size_rcons powS ?size_ge0.
(have {2}->: 2=1+1 by done); rewrite mulrDl mul1r ltr_le_add //.
by rewrite ler_pimulr ?b2i_le1 ltrW powPos.
qed.

(* -------------------------------------------------------------------- *)
lemma bs2intK s : int2bs (size s) (bs2int s) = s.
proof.
elim/last_ind: s=> /= [|s b ih]; 1: by rewrite bs2int_nil int2bs0s.
rewrite bs2int_rcons size_rcons int2bsS ?size_ge0; congr.
  rewrite -(@bs2int_mod (size s)) 1:-bs2int_rcons ?bs2int_ge0.
  by rewrite mulrC modzMDr bs2int_mod 1:bs2int_ge0.
have gt0_2Xs: 0 < 2  ^ (size s) by rewrite powPos.
rewrite mulrC divzMDr 1:gtr_eqF // divz_small /=.
  by rewrite bs2int_ge0 gtr0_norm ?bs2int_le2Xs.
by rewrite mod2_b2i b2i_eq0.
qed.

(* -------------------------------------------------------------------- *)
lemma int2bsK N i : 0 <= i < 2^N => bs2int (int2bs N i) = i.
proof.
elim/natind: N i=> [n le0_n|n ge0_n ih] i.
  rewrite powNeg // ltz1 -eqr_le => <-; rewrite int2bs0.
  by rewrite nseq0_le // bs2int_nil.
case=> [ge0_i lt_i2XSn]; rewrite int2bsS // bs2int_rcons.
rewrite -{1}bs2int_mod // ih 1:ltz_pmod ?powPos //=.
  by rewrite modz_ge0 gtr_eqF ?powPos.
rewrite size_int2bs max_ler // eq_sym {1}(@divz_eq i (2^n)).
rewrite addrC mulrC; do 2! congr; move: lt_i2XSn.
rewrite powS // -ltz_divLR ?powPos // => lt.
rewrite -{1}(@modz_small (i %/ 2^n) 2) ?ger0_norm ?b2i_mod2 //.
by rewrite lt /= divz_ge0 ?powPos.
qed.
