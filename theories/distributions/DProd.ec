(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List StdOrder Distr StdOrder.
(*---*) import RealOrder RealSeries StdBigop.Bigreal BRA.

pragma +implicits.
pragma -oldip.

(* -------------------------------------------------------------------- *)
op mprod ['a,'b] (ma : 'a -> real) (mb : 'b -> real) (ab : 'a * 'b) =
  (ma ab.`1) * (mb ab.`2).

(* -------------------------------------------------------------------- *)
lemma isdistr_mprod ['a 'b] ma mb :
  isdistr<:'a> ma => isdistr<:'b> mb => isdistr (mprod ma mb).
proof.
move=> isa isb; split=> [x|s uqs].
+ by apply/mulr_ge0; apply/ge0_isdistr.
(* FIXME: This instance should be in bigops *)
rewrite (@partition_big ofst _ predT _ _ (undup (unzip1 s))).
+ by apply/undup_uniq.
+ by case=> a b ab_in_s _; rewrite mem_undup map_f /mprod.
pose P := fun x ab => ofst<:'a, 'b> ab = x.
pose F := fun (ab : 'a * 'b) => mb ab.`2.
rewrite -(@eq_bigr _ (fun x => ma x * big (P x) F s)) => /= [x _|].
+ by rewrite mulr_sumr; apply/eq_bigr=> -[a b] /= @/P <-.
pose s' := undup _; apply/(@ler_trans (big predT (fun x => ma x) s')).
+ apply/ler_sum=> a _ /=; apply/ler_pimulr; first by apply/ge0_isdistr.
  rewrite -big_filter -(@big_map snd predT) le1_sum_isdistr //.
  rewrite map_inj_in_uniq ?filter_uniq //; case=> [a1 b1] [a2 b2].
  by rewrite !mem_filter => @/P @/ofst @/osnd |>.
by apply/le1_sum_isdistr/undup_uniq.
qed.

(* -------------------------------------------------------------------- *)
op (`*`) (da : 'a distr) (db : 'b distr) =
  mk (mprod (mu1 da) (mu1 db))
axiomatized by dprod_def.

(* -------------------------------------------------------------------- *)
lemma dprod1E (da : 'a distr) (db : 'b distr) a b:
  mu1 (da `*` db) (a,b) = mu1 da a * mu1 db b.
proof. rewrite dprod_def -massE muK // isdistr_mprod isdistr_mu1. qed.

(* -------------------------------------------------------------------- *)
lemma dprodE Pa Pb (da : 'a distr) (db : 'b distr):
    mu (da `*` db) (fun (ab : 'a * 'b) => Pa ab.`1 /\ Pb ab.`2)
  = mu da Pa * mu db Pb.
proof. admitted.

(* -------------------------------------------------------------------- *)
lemma supp_dprod (da : 'a distr) (db : 'b distr) ab:
  ab \in da `*` db <=> ab.`1 \in da /\ ab.`2 \in db.
proof.
by case: ab => a b /=; rewrite !supportP dprod1E; smt(mu_bounded).
qed.

(* -------------------------------------------------------------------- *)
lemma weight_dprod (da : 'a distr) (db : 'b distr):
  weight (da `*` db) = weight da * weight db.
proof.
pose F := fun ab : 'a * 'b => predT ab.`1 /\ predT ab.`2.
by rewrite (@mu_eq _ _ F) // dprodE.
qed.

(* -------------------------------------------------------------------- *)
lemma dprod_ll (da : 'a distr) (db : 'b distr):
  is_lossless (da `*` db) <=> is_lossless da /\ is_lossless db.
proof. by rewrite /is_lossless weight_dprod [smt(mu_bounded)]. qed.

(* -------------------------------------------------------------------- *)
lemma dprod_uni (da : 'a distr) (db : 'b distr):
  is_uniform da => is_uniform db => is_uniform (da `*` db).
proof.
move=> da_uni db_uni [a b] [a' b']; rewrite !supp_dprod !dprod1E /=.
by case=> /da_uni ha /db_uni hb [/ha-> /hb->].
qed.

(* -------------------------------------------------------------------- *)
lemma dprod_funi (da : 'a distr) (db : 'b distr):
  is_funiform da => is_funiform db => is_funiform (da `*` db).
proof.
move=> da_uni db_uni [a b] [a' b']; rewrite !dprod1E.
by congr; [apply da_uni | apply db_uni].
qed.

(* -------------------------------------------------------------------- *)
lemma dprod_fu (da : 'a distr) (db : 'b distr):
  is_full (da `*` db) <=> (is_full da /\ is_full db).
proof.
split=> [h|[] ha hb].
+ by split=> [a|b]; [move: (h (a,witness))|move: (h (witness,b))]; rewrite supp_dprod.
by move=> [] a b; rewrite supp_dprod ha hb.
qed.

(* -------------------------------------------------------------------- *)
(* TODO : generalize this to parametric distribution *)
abstract theory ProdSampling.
type t1, t2.

op d1 : t1 distr.
op d2 : t2 distr.

module S = {
  proc sample () : t1 * t2 = {
    var r;

    r <$ d1 `*` d2;
    return r;
  }

  proc sample2 () : t1 * t2 = {
    var r1, r2;

    r1 = $ d1;
    r2 = $ d2;
    return (r1,r2);
  }
}.

equiv sample_sample2 : S.sample ~ S.sample2 : true ==> ={res}.
proof.
bypr (res{1}) (res{2}) => // &m1 &m2 a.
have ->: Pr[S.sample() @ &m1 : res = a] = mu1 (d1 `*` d2) a.
+ by byphoare=> //=; proc; rnd; skip. 
elim: a=> a1 a2; have -> := dprod1E d1 d2 a1 a2.
byphoare=> //=.
proc; seq  1: (r1 = a1) (mu1 d1 a1) (mu1 d2 a2) _ 0%r true=> //=.
+ by rnd.  
+ by rnd.
by hoare; auto=> /> ? ->.
qed.
end ProdSampling.
