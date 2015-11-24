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
(*---*) import IntID IntOrder Bigint.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op bs2int (s : bool list) =
  BIA.bigi predT (fun i => 2^i * b2i (nth false s i)) 0 (size s).

op int2bs (N n : int) =
  mkseq (fun i => (n %/ 2^i) %% 2 <> 0) N.

lemma size_int2bs N n : size (int2bs N n) = max 0 N.
proof. by apply/size_mkseq. qed.

lemma bs2intS b (s : bool list):
  bs2int (rcons s b) = (bs2int s) + 2^(size s) * (b2i b).
proof.
rewrite /bs2int size_rcons BIA.big_int_recr ?size_ge0 //=.
rewrite nth_rcons (@ltrr (size s)) /=; congr.
by apply/BIA.eq_big_int=> i [_ lt_is] /=; rewrite nth_rcons lt_is.
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
