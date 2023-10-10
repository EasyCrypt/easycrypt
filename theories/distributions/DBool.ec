(* -------------------------------------------------------------------- *)
require import AllCore List Distr Ring Number.
require import StdRing StdOrder StdBigop RealSeq RealSeries.
require (*--*) Bigop Bigalg.
(*---*) import RField RealOrder Bigreal Bigreal.BRA.

(* -------------------------------------------------------------------- *)
clone include Distr.MFinite with
  type t            <- bool,
  op Support.enum <- [true; false],
  op Support.card <- 2
  rename "dunifinE" as "dboolE_count"
  rename "dunifin" as "dbool"
proof Support.enum_spec by case.

lemma dboolE (E : bool -> bool):
  mu dbool E =   (if E true  then 1%r/2%r else 0%r)
               + (if E false then 1%r/2%r else 0%r).
proof. rewrite !dboolE_count /= /b2i /#. qed.

lemma dbool_leq b1 b2:
  (b1 => b2) =>
  mu1 dbool b1 <= mu1 dbool b2.
proof. by case b1; case b2=> //=; rewrite 2!dbool1E. qed.

(* -------------------------------------------------------------------- *)
theory Biased.
op clamp (p : real) = maxr 0%r (minr 1%r p).

lemma clamp_ge0 p : 0%r <= clamp p by move=> /#.
lemma clamp_le1 p : clamp p <= 1%r by move=> /#.

lemma clamp_id (p : real) : 0%r <= p <= 1%r => clamp p = p.
proof. by move=> /#. qed.

op mbiased (p : real) =
  fun b => if b then clamp p else 1%r - clamp p.

lemma ge0_mbiased (p : real) :
  forall b, 0%r <= mbiased p b.
proof. by move=> /#. qed.

lemma isdistr_mbiased p : isdistr (mbiased p).
proof.
apply/(isdistr_finP [true; false])=> //.
  by case. by apply/ge0_mbiased.
by rewrite 2!big_cons big_nil => @/predT /= /#.
qed.

op dbiased (p : real) = Distr.mk (mbiased p).

lemma dbiased1E (p : real) (b : bool) :
  mu1 (dbiased p) b =
   if b then clamp p else 1%r - clamp p.
proof. by rewrite muK  // isdistr_mbiased. qed.

lemma dbiasedE (p : real) (E : bool -> bool) :
  mu (dbiased p) E =
      (if E true  then       clamp p else 0%r)
    + (if E false then 1%r - clamp p else 0%r).
proof. by rewrite muE sum_bool /= !dbiased1E. qed.

lemma supp_dbiased (p : real) b :
  0%r < p < 1%r => b \in (dbiased p).
proof.
case=> gt0_p lt1_p; rewrite /support dbiased1E /#.
qed.

lemma dbiased_ll (p : real) : is_lossless (dbiased p).
proof. by rewrite /is_lossless dbiasedE /predT /= addrCA. qed.

lemma dbiased_fu (p : real) :
  0%r < p < 1%r => is_full (dbiased p).
proof.
by move=> ??;rewrite supp_dbiased.
qed.

lemma dmap_pred (d: 'a distr) (p: 'a -> bool) :
  is_lossless d =>
  dmap d p = dbiased (mu d p).
proof.
move => d_ll; apply eq_distr => x.
rewrite dbiased1E clamp_id; first by smt(ge0_mu le1_mu).
rewrite dmap1E /(\o) /pred1 /=. 
by move : (mu_not d p) => /#.
qed.

lemma dbiased1 : dbiased 1%r = dunit true.
proof. by rewrite eq_distr => b; rewrite dbiased1E dunit1E /#. qed.

lemma dbiased0 : dbiased 0%r = dunit false.
proof. by rewrite eq_distr => b; rewrite dbiased1E dunit1E /#. qed.

lemma marginal_sampling_pred (d : 'a distr) (p : 'a -> bool) :
  is_lossless d =>
  d = dlet (dbiased (mu d p)) 
           (fun b => if b then (dcond d p) else (dcond d (predC p))).
proof.
move => d_ll; rewrite -dmap_pred // {1}(marginal_sampling d p).
by congr; apply fun_ext => -[|] /=; congr => /#.
qed.

end Biased.

(* -------------------------------------------------------------------- *)
abstract theory FixedBiased.

import Biased.

op p : {real | 0%r < p < 1%r} as in01_p.

op dbiased = Biased.dbiased p.

lemma dbiased1E (b : bool) :
  mu1 dbiased b = if b then p else 1%r - p.
proof. rewrite dbiased1E clamp_id //; smt (in01_p). qed.

lemma dbiasedE (E : bool -> bool) :
  mu dbiased E =
      (if E true  then       p else 0%r)
    + (if E false then 1%r - p else 0%r).
proof. rewrite dbiasedE !clamp_id //;smt(in01_p). qed.

lemma supp_dbiased x : x \in dbiased.
proof. by apply supp_dbiased;apply in01_p. qed.

lemma dbiased_ll : is_lossless dbiased.
proof. by apply dbiased_ll;apply in01_p. qed.

lemma dbiased_fu : is_full (dbiased p).
proof. by move=> ?;rewrite supp_dbiased. qed.

end FixedBiased.

(* -------------------------------------------------------------------- *)
import Biased Bigreal.

abstract theory DFunBiased.
type t.

clone import MUniFinFun with type t <- t.

op dbfun (ps : t -> real) =
  dfun (fun x => dbiased (ps x)).

abbrev dbfun0 (c : real) =
  dbfun (fun _ => c).

lemma dbfunE (c : real) (pT pF : t -> bool) :
  0%r <= c <= 1%r => (forall x, !(pT x /\ pF x)) =>

  mu (dbfun0 c) (fun f =>
         (forall x, pT x =>  f x)
      /\ (forall x, pF x => !f x)) =

    (      c) ^ (count pT FinT.enum)
  * (1%r - c) ^ (count pF FinT.enum).
proof.
move=> rgc h; pose Q x b := (pT x => b) /\ (pF x => !b).
rewrite -(mu_eq _ (fun f => forall x, Q x (f x))) /= 1:/#.
rewrite dfunE (@BRM.bigID _ _ pT) !predTI /=.
rewrite -(BRM.eq_bigr _ (fun _ => clamp c)).
- move=> x @/Q /= ^pTx -> /=; rewrite -(mu_eq _ (pred1 true)).
  - by case=> //=; case: (pF x) (h x). - by rewrite dbiased1E.
rewrite mulr_const_cond clamp_id //; congr; rewrite (@BRM.bigID _ _ pF).
rewrite  -(BRM.eq_bigr _ (fun _ => 1%r - clamp c)).
- move=> x [_] @/Q /= ^pFx -> /=; rewrite -(mu_eq _ (pred1 false)).
  - by case=> //=; case: (pT x) (h x). - by rewrite dbiased1E.
rewrite mulr_const_cond clamp_id // -(BRM.eq_bigr _ (fun _ => 1%r)).
- move=> x /= @/predC [pTNx pFNx]; rewrite -(mu_eq _ predT).
  - by move=> b @/predT @/Q; rewrite pTNx pFNx.
  by rewrite dbiased_ll.
rewrite mulr_const_cond expr1z mulr1; congr; apply: eq_count.
by move=> x @/predI @/predC; case: (pT x) (pF x) (h x).
qed.

lemma dbfunE_mem_uniq (c: real) (lT lF : t list) : 
  0%r <= c <= 1%r => uniq lT => uniq lF => 
  (forall x, !(x \in lT /\ x \in lF)) =>
  mu (dbfun0 c) (fun f => 
         (forall x, x \in lT => f x)
      /\ (forall x, x \in lF => !f x)) =
    (      c) ^ (size lT)
  * (1%r - c) ^ (size lF).
proof.
move=> hc huT huF hd; have := dbfunE c (mem lT) (mem lF) hc hd.
by rewrite !FinT.count_mem.
qed.

lemma dbfunE_mem_le (c: real) (lT lF : t list) : 
  0%r <= c <= 1%r =>
  (forall x, !(x \in lT /\ x \in lF)) =>
  c ^ (size lT) * (1%r - c) ^ (size lF) <= 
    mu (dbfun0 c) (fun f => 
         (forall x, x \in lT => f x)
      /\ (forall x, x \in lF => !f x)).
proof.
move=> [h0c hc1] hl; have /ler_trans:
  c ^ (size lT) * (1%r - c) ^ (size lF) <=
    c ^ (size (undup lT)) * (1%r - c) ^ (size (undup lF)).
+ apply/ler_pmul; try by apply expr_ge0=> //#.
  + by rewrite &(ler_wiexpn2l) 1://# size_undup size_ge0.
  + by rewrite &(ler_wiexpn2l) 1://# size_undup size_ge0.
apply; rewrite -(dbfunE_mem_uniq _ (undup _)) // ?undup_uniq.
+ by move=> x; rewrite !mem_undup hl.
+ by apply mu_le => /= f _; smt (mem_undup).
qed.

lemma dbfun_split (ps ps1 ps2 : t -> real) :
     (forall x, 0%r <= ps x <= 1%r)
  => (forall x, 0%r <= ps1 x <= 1%r)
  => (forall x, 0%r <= ps2 x <= 1%r)
  => (forall x, ps x = ps1 x * ps2 x)
  =>   dbfun ps
     = dmap
         (dbfun ps1 `*` dbfun ps2)
         (fun (fg : _ * _) x => (fg.`1 x) /\ (fg.`2 x)).
proof.
pose F (fg : (t -> bool) * (t -> bool)) := fun x => (fg.`1 x, fg.`2 x).
pose G (bb : t -> bool * bool) := fun x => (bb x).`1 /\ (bb x).`2.
move=> *; rewrite -(@eq_dmap _ (G \o F)); first by apply/fun_ext.
rewrite -dmap_comp /F -dfun_prodE /= /G => {F G}.
apply/eq_distr=> h; rewrite dmap1E /(\o) /pred1 /=.
pose p (x : t) (bb : _ * _) := (bb.`1 /\ bb.`2) = h x.
rewrite -(mu_eq _ (fun F => forall x, p x (F x))) /=.
- move=> F; apply: eq_iff; split.
  - by move=> hp; apply/fun_ext/hp.
  - by move/fun_ext; apply.
rewrite dfunE dfun1E; apply: BRM.eq_bigr => /= x _ @/p.
rewrite dprod_dlet dletE_bool /= !dletE_bool /= !dunitE /=.
rewrite !mulrDr !mulrA; case: (h x) => //= _;
  by rewrite !dbiased1E /= !clamp_id; move: x => //#.
qed.

lemma dfun_biased_biased (lambda : real) (ps : t -> real) :
     (0%r < lambda < 1%r)
  => (forall x, 0%r <= ps x <= lambda)
  =>   dbfun ps
     = dmap
         (dbfun0 lambda `*` dbfun (fun x => ps x / lambda))
         (fun (fg : _ * _) => fun x => fg.`1 x /\ fg.`2 x).
proof.
move=> *; rewrite &(dbfun_split) //= => *;
  by rewrite ?(ler_pdivl_mulr, ler_pdivr_mulr) //#.
qed.
end DFunBiased.

(* -------------------------------------------------------------------- *)
abstract theory Cost.
  op cdbool : { int | 0 <= cdbool } as ge0_cdbool.
  
  schema cost_dbool `{P} : cost [P: dbool] = N cdbool.
  hint simplify cost_dbool.
end Cost.
