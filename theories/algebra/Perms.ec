(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv Binomial Ring StdOrder.
(*---*) import IntID IntOrder.

(* -------------------------------------------------------------------- *)
op allperms_r (n : unit list) (s : 'a list) : 'a list list.

axiom allperms_r0 (s : 'a list) :
  allperms_r [] s = [[]].

axiom allperms_rS (x : unit) (n : unit list) (s : 'a list) :
  allperms_r (x :: n) s = flatten (
    map (fun x => map ((::) x) (allperms_r n (rem x s))) (undup s)).

op allperms (s : 'a list) = allperms_r (nseq (size s) tt) s.

hint rewrite ap_r : allperms_r0 allperms_rS.

(* -------------------------------------------------------------------- *)
lemma nosmt allperms_rP n (s t : 'a list) : size s = size n =>
  (mem (allperms_r n s) t) <=> (perm_eq s t).
proof.
elim: n s t => [s t /size_eq0 ->|_ n ih s t] //=; rewrite ?ap_r /=.
  split => [->|]; first by apply/perm_eq_refl.
  by move/perm_eq_sym; apply/perm_eq_small.
case: s=> [|x s]; first by rewrite addz_neq0 ?size_ge0.
(pose s' := undup _)=> /=; move/addrI=> eq_sz; split.
  move/flatten_mapP=> [y] [s'y] /= /mapP [t'] [+ ->>].
  case: (x = y)=> [<<-|]; first by rewrite ih // perm_cons.
  move=> ne_xy; have sy: mem s y.
    by have @/s' := s'y; rewrite mem_undup /= eq_sym ne_xy.
  rewrite ih /= ?size_rem // 1?addrCA //.
  move/(perm_cons y); rewrite perm_consCA => /perm_eqrE <-.
  by apply/perm_cons/perm_to_rem.
move=> ^eq_st /perm_eq_mem/(_ x) /= tx; apply/flatten_mapP=> /=.
have nz_t: t <> [] by case: (t) tx. exists (head x t) => /=.
have/perm_eq_mem/(_ (head x t)) := eq_st; rewrite /s' mem_undup.
move=> ->; rewrite -(mem_head_behead x) //=; apply/mapP.
case: (x = head x t)=> /= [xE|nex].
  exists (behead t); rewrite head_behead //= ih //.
  by rewrite -(perm_cons x) {2}xE head_behead.
have shx: mem s (head x t).
  move/perm_eq_mem/(_ (head x t)): eq_st => /=; rewrite eq_sym.
  by rewrite nex /= => ->; rewrite -(mem_head_behead x).
exists (behead t); rewrite head_behead //= ih /=.
  by rewrite size_rem // addrCA.
rewrite -(perm_cons (head x t)) head_behead // perm_consCA.
by have/perm_eqrE <- := eq_st; apply/perm_cons/perm_eq_sym/perm_to_rem.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt uniq_allperms_r n (s : 'a list) : uniq (allperms_r n s).
proof.
elim: n s => [|_ n ih] s; rewrite ?ap_r  //.
apply/uniq_flatten_map/undup_uniq.
  by move=> x /=; apply/map_inj_in_uniq/ih => a b _ _ [].
move=> x y; rewrite !mem_undup => sx sy /= /hasP[t].
by case=> /mapP[t1] [st1 ->] /mapP[t2] [st2 [->]].
qed.

(* -------------------------------------------------------------------- *)
lemma allpermsP (s t : 'a list) : mem (allperms s) t <=> perm_eq s t.
proof. by apply/allperms_rP; rewrite size_nseq ler_maxr ?size_ge0. qed.

(* -------------------------------------------------------------------- *)
lemma uniq_allperms (s : 'a list) : uniq (allperms s).
proof. by apply/uniq_allperms_r. qed.

(* -------------------------------------------------------------------- *)
lemma allperms_spec (s t : 'a list) :
  count (pred1 t) (allperms s) = b2i (perm_eq s t).
proof. by rewrite count_uniq_mem 1:uniq_allperms // allpermsP. qed.

(* -------------------------------------------------------------------- *)
require import StdBigop.
(*---*) import Bigint Bigint.BIM Bigint.BIA.

(* -------------------------------------------------------------------- *)
lemma size_allperms_uniq_r n (s : 'a list) : size s = size n => uniq s =>
  size (allperms_r n s) = fact (size s).
proof.
elim: n s => /= [|_ n ih] s; rewrite ?ap_r /=.
  by move/size_eq0=> -> /=; rewrite fact0.
case: s=> [|x s]; first by rewrite addz_neq0 ?size_ge0.
(pose s' := undup _)=> /=; move/addrI=> eq_sz [Nsz uqs].
rewrite (addrC 1) factS ?size_ge0 // -ih //.
rewrite size_flatten sumzE -map_comp; pose F := _ \o _.
rewrite /s' undup_id //= big_consT /= {1}/F /(\o) /=.
rewrite size_map /= mulrDl /= addrC; congr.
have: forall y, mem s y => F y = size (allperms_r n s).
  move=> y sy @/F @/(\o); rewrite size_map; case: (x = y)=> //.
  move=> ne_xy; rewrite !ih //= ?size_rem //.
    by rewrite rem_uniq //=; apply/negP=> /mem_rem.
move/eq_in_map=> ->; rewrite big_map predT_comp /(\o) /=.
by rewrite sumr_const intmulz count_predT mulrC.
qed.

(* -------------------------------------------------------------------- *)
lemma size_allperms_uniq (s : 'a list) :
  uniq s => size (allperms s) = fact (size s).
proof. by apply/size_allperms_uniq_r; rewrite size_nseq ler_maxr ?size_ge0. qed.
