(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List StdBigop StdOrder IntDiv Distr.
(*---*) import IntOrder Bigint MUniform Range.

(* -------------------------------------------------------------------- *)
(* We keep intervals closed for now, to justify attaching the [_.._]
   notation to this distribution. *)
op dinter (i j : int) = duniform (range i (j + 1)).

lemma dinter1E (i j : int) x:
  mu1 (dinter i j) x = if (i <= x <= j) then 1%r/(j - i + 1)%r else 0%r.
proof. by rewrite duniform1E mem_range undup_id 1:range_uniq size_range /#. qed.

lemma dinterE (i j : int) P:
  mu (dinter i j) P
  = (size (filter P (range i (j + 1))))%r / (max 0 (j - i + 1))%r.
proof. by rewrite duniformE undup_id 1:range_uniq size_range size_filter /#. qed.

lemma weight_dinter (i j : int):
  weight (dinter i j) = b2r (i <= j).
proof. by rewrite /weight dinterE filter_predT size_range /#. qed.

lemma supp_dinter (i j : int) x:
  x \in (dinter i j) <=> i <= x <= j.
proof. by rewrite /support /in_supp dinter1E; case (i <= x <= j)=> //= /#. qed.

lemma dinter_ll (i j : int): i <= j => is_lossless (dinter i j).
proof. move=> Hij;apply /drange_ll => /#. qed.

lemma dinter_uni (i j : int): is_uniform (dinter i j).
proof. apply drange_uni. qed.

(* -------------------------------------------------------------------- *)
lemma duni_range_dvd (p q : int) : 0 < p => 0 < q => q %| p =>
  dmap (dinter 0 (p-1)) (fun x => x %% q) = dinter 0 (q-1).
proof.
move=> gt0_p gt0_q dvd_qp; apply/eq_distr=> i; apply/eq_sym.
rewrite dinter1E ler_subr_addl (addrC 1) -ltzE -mem_range.
case: (i \in range 0 q) => /= [/mem_range [ge0i lei]|Nrgi]; last first.
- pose d := dmap _ _; suff /supportPn/eq_sym //: !(i \in d).
  apply: contra Nrgi => /supp_dmap[j [/supp_dinter [ge0j lej] /=]].
  by move=> ->>; rewrite mem_range modz_ge0 1:gtr_eqF //= ltz_pmod.
pose s := flatten (map
  (fun k => map (fun i : int => k * q + i) (range 0 q)) (range 0 (p %/ q))).
have uniq_s: uniq s; first apply: uniq_flatten_map.
- move=> j /=; rewrite map_inj_in_uniq ?range_uniq.
  by move => x y _ _ /=; apply/addrI.
- move=> x y /mem_range rg_x /mem_range rg_y /hasP /=.
  case=> j [/mapP[/= k [/mem_range rg_k]] ->>].
  by case/mapP=> l [/mem_range rg_l] {rg_x} {rg_y} /#.
- by apply: range_uniq.
have mem_s: forall x, (x \in s) <=> (x \in range 0 p).
- move=> x; rewrite mem_range; split.
  - case/flatten_mapP=> j [/= /mem_range rgj] /=.
    case/mapP => [k [/mem_range rgk]] ->>; smt(@IntDiv).
  - case=> ge0x lex; apply/flatten_mapP => /=.
    exists (x %/ q); rewrite mem_range.
    rewrite divz_ge0 // ge0x /=; split; 1: smt(@IntDiv).
    apply/mapP; exists (x %% q); rewrite mem_range.
    rewrite modz_ge0 1:gtr_eqF //= ltz_pmod //= &(divz_eq).
have eqs: perm_eq s (range 0 p).
- by apply: uniq_perm_eq => //; apply/range_uniq.
rewrite dmap1E duniformE /= undup_id ?range_uniq /pred1 /(\o).
rewrite size_range /max gt0_p /=; have := perm_eqP s (range 0 p).
case=> + _ - /(_ eqs) <- @/s; rewrite count_flatten sumzE /=.
pose t := map _ _; rewrite BIA.big_seq -(BIA.eq_bigr _ (fun _ => 1)) /=.
- move=> k /mapP[xs [/mapP[j [/mem_range [ge0j lej]] ->>]] ->>].
  rewrite count_map /preim -(eq_in_count (pred1 i)) => [k|].
  - by case/mem_range=> [ge0k lek] /=; rewrite modzMDl pmod_small.
  by rewrite eq_sym count_uniq_mem ?range_uniq mem_range ge0i lei.
rewrite -(BIA.big_seq _ t) big_constz count_predT !size_map.
rewrite size_range /= /max; case/dvdzP: dvd_qp => r ->>.
have gt0_r : 0 < r by apply: (pmulr_lgt0 q).
rewrite mulzK 1:gtr_eqF // fromintM gt0_r /=.
rewrite  RField.invrM ?eq_fromint 1,2:gtr_eqF //.
by rewrite RField.mulrCA RField.divff // eq_fromint gtr_eqF.
qed.
