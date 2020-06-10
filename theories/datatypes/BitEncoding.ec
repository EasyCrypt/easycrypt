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

lemma nosmt int2bsS N i : 0 <= N =>
  int2bs (N + 1) i = rcons (int2bs N i) ((i %/ 2^N) %% 2 <> 0).
proof. by apply/mkseqS. qed.

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

lemma nosmt bs2int_mod N i : 0 <= i => int2bs N (i %% 2^N) = int2bs N i.
proof.
move=> ge0_i; apply/bs2int_eq=> //; last by rewrite modz_mod.
by rewrite modz_ge0 // -lt0n ?ltrW // expr_gt0.
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
rewrite -(@bs2int_mod (size s)) 1:-bs2int_rcons ?bs2int_ge0.
rewrite mulrC modzMDr bs2int_mod 1:bs2int_ge0 ih; congr.
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
rewrite -{1}bs2int_mod // ih 1:ltz_pmod ?expr_gt0 //=.
  by rewrite modz_ge0 gtr_eqF ?expr_gt0.
rewrite size_int2bs ler_maxr // eq_sym {1}(@divz_eq i (2^n)).
rewrite addrC mulrC; do 2! congr; move: lt_i2XSn.
rewrite exprS // -ltz_divLR ?expr_gt0 // => lt.
rewrite -{1}(@modz_small (i %/ 2^n) 2) ?ger0_norm ?b2i_mod2 //.
by rewrite lt /= divz_ge0 ?expr_gt0.
qed.
end BS2Int.

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
