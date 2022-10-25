require import AllCore Distr DBool List Dexcepted DInterval .
(*   *) import StdOrder RField RealOrder StdBigop Bigreal BRA.

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Small Range Definition Property                                            *)

abstract theory DFunSmallRange.

type X.
clone import MUniFinFun as MUFF with
  type t <- X.   (* This assumes that the type of from is finite *)


op difun r = dfun (fun _ => [0..r-1]).

lemma pr_difun_l_pow r x (l:X list) q i :
  0 <= i < r =>  
  !x \in l => size l <= q =>  
  1.0/r%r * (1.0 - 1.0 / r%r)^q <= 
    mu (difun r) (fun fr => fr x = i /\ forall m', m' \in l => fr m' <> i).
proof.
  move=> hi hm hl.
  pose lam := 1.0/r%r.
  apply (ler_trans (lam ^ 1 * (1%r - lam) ^ size l)).
  + rewrite RField.expr1; apply ler_wpmul2l; 1: smt().
    apply ler_wiexpn2l; [1:smt ()| 2: smt(size_ge0)].
  apply (ler_trans _ _ _ 
    (dfunE_mem_le lam (fun _ => [0..r-1]) [x] l (fun _ => pred1 i) _ _ _)) => /=.
  + by apply dinter_ll => /#. + by rewrite dinter1E /#. + smt().
  by apply mu_le => /#.
qed.

lemma pr_difun_l r x (l:X list) q i :
  0 <= i < r =>  
  !x \in l => size l <= q =>  
  1.0/r%r * (1.0 - q%r / r%r) <= 
    mu (difun r) (fun fr => fr x = i /\ forall m', m' \in l => fr m' <> i).
proof.
  move=> i_bound hm hl.
  apply: ler_trans (pr_difun_l_pow _ _ _ _ _ i_bound hm hl).
  apply ler_wpmul2l; 1: smt(). 
  apply le_binomial => //; smt(size_ge0).
qed.

end DFunSmallRange.

abstract theory DFunBiasedSingle.
(* Used by semi constant distribution QROM theory.
   Should we clone fixedbiased here and then use this
   in mixed bias? 
   The semi constant theorem is defined for a fixed lambda, 
   so this should be fine. 
   Then we would call this fixed. *)

type X.

clone import MUniFinFun as MUFF with
  type t <- X.   (* This assumes that the type of from is finite *)

op dbfun lam = dfun (fun _ => Biased.dbiased lam).

lemma dbfun_ll lam : is_lossless (dbfun lam).
proof. apply/dfun_ll => /=; apply/Biased.dbiased_ll. qed.
hint solve 0 random : dbfun_ll.

lemma pr_dbfun_l_eq lam x (l:X list) :
  0%r <= lam <= 1%r =>
  !x \in l => uniq l =>
  mu (dbfun lam) (fun (t : X -> bool) => t x /\ forall x', x' \in l => ! t x') =
    lam * (1%r - lam) ^ size l.
proof.
  move=> lam_bound hx hl; apply (eq_trans _ (lam ^ (size [x]) * (1%r - lam) ^ size l)); last first.
  + by rewrite /= RField.expr1.
  rewrite -(dfunE_mem_uniq lam (fun _ => Biased.dbiased lam) [x] l (fun _ => pred1 true)) //=.
  + by apply Biased.dbiased_ll. + by rewrite Biased.dbiased1E /= Biased.clamp_id. + smt().
  by apply mu_eq => /#.
qed.

lemma pr_dbfun_l_pow lam x (l:X list) q : 
  0%r <= lam <= 1%r =>
  !x \in l => size l <= q =>  
  lam*(1%r-lam)^q <= 
    mu (dbfun lam) (fun t => t x /\ forall x', x' \in l => !t x').
proof.
  move=> lam_bound hm hl.
  apply (ler_trans (lam ^ 1 * (1%r - lam) ^ size l)).
  + rewrite RField.expr1; apply ler_wpmul2l; 1: by case: lam_bound.
    apply ler_wiexpn2l; [1:smt ()| 2: smt(size_ge0)].
  apply (ler_trans _ _ _ 
    (dfunE_mem_le lam (fun _ => Biased.dbiased lam) [x] l (fun _ => pred1 true) _ _ _)) => /=.
  + by apply Biased.dbiased_ll. + by rewrite Biased.dbiased1E /= Biased.clamp_id. + smt().
  by apply mu_le => /#.
qed.

lemma pr_dbfun_l lam x (l:X list) q : 
  0%r <= lam <= 1%r =>
  !x \in l => size l <= q =>  
  lam*(1%r-q%r * lam) <= 
    mu (dbfun lam) (fun t => t x /\ forall x', x' \in l => !t x').
proof.
  move=> lam_bound hm hl.
  apply: ler_trans (pr_dbfun_l_pow _ _ _ _ lam_bound hm hl).
  apply ler_wpmul2l; 1: by case: lam_bound.
  apply le_binomial => //; smt(size_ge0).
qed.

end DFunBiasedSingle.

abstract theory DFunBiasedMulti.
(* Used below for mix lambda reduction *)

import Biased.

type X.

clone import MUniFinFun as MUFF with
  type t <- X.   (* This assumes that the type of from is finite *)

op dfun_biased(ps : X -> real) = dfun (fun x => Biased.dbiased (ps x)).

lemma dfun_biasedP x b ps :
  (forall x0,   0%r <= ps x0 <= 1%r) => 
  mu (dfun_biased ps) (fun bf => bf x = b) =
      if b then ps x else 1%r - ps x.
proof.
move => Hps.
rewrite /dfun_biased.  
move : (dfun_allE_cond (if b then ps x else 1%r - ps x) (fun (x0 : X) => dbiased (ps x0)) (fun x0 => x = x0) (pred0) (fun x0 b' => x = x0 /\ b = b') _ _ _) => /=. 
+ by move => x0 /=; apply dbiased_ll.
+ by move => x0 /=; rewrite dbiasedE !clamp_id /=; by smt(). 
+ by smt().
have -> : ((=)x) = pred1 x;1: by smt(). 
rewrite FinT.enum_spec /= count_pred0 /= RField.expr0 RField.expr1 /= /#. 
 qed.

lemma supp_dfun_biased f ps :
  (forall x0,   0%r < ps x0 < 1%r) =>  
    f \in (dfun_biased ps).
proof. 
move => Hps; apply dfun_supp => /= x. 
by apply supp_dbiased; smt(). 
qed.

lemma dfun_biased_ll ps : is_lossless (dfun_biased ps)
 by  apply dfun_ll => // x; apply dbiased_ll;apply in01_p. 

lemma dfun_biased_fu ps :
  (forall x0,   0%r < ps x0 < 1%r) => 
     is_full (dfun_biased ps).
proof.
by move=> ?;rewrite /is_full => x; apply supp_dfun_biased => //.
qed.

end DFunBiasedMulti.

abstract theory MixLambdaDFun.

clone import DFunBiasedMulti as DFBM.

import MUFF.
import Biased.

clone import DFunBiasedSingle with
    type X <- X,
    theory MUFF <- MUFF
    proof *.

module MixLambda = {
   proc left(ps : X -> real) = {
       var h;
       h <$ dfun_biased ps;
       return h;
   } 

   proc right(lambda : real, ps : X -> real) = {
       var g, h, ps_r, keep1;
       ps_r <- fun x => ps x / lambda;
       g <$ dbfun lambda;
       keep1 <$ dfun_biased ps_r;
       h <- fun x => g x /\ keep1 x;
       return h;
   } 
}.

lemma distr_equality _ps lambda :
  0%r < lambda < 1%r  =>
 (forall x,
   0%r <= _ps x && _ps x <= lambda) => 
  (dlet (dbfun lambda)
     (fun (g : X -> bool) =>
        dmap (dfun_biased (fun (x : X) => _ps x / lambda)) (fun (keep1 : X -> bool) (x : X) => g x /\ keep1 x))) = 
    dfun_biased _ps.
proof.
move => lambda_01 Hx.
apply eq_distr => h.
have -> : 
  (dlet (dbfun lambda)
     (fun (g : X -> bool) =>
        dmap (dfun_biased (fun (x : X) => _ps x / lambda)) (fun (keep1 : X -> bool) (x : X) => g x /\ keep1 x))) = 
  dlet (dbfun lambda) 
          (fun bf => dmap (dfun_biased (fun (x : X) => _ps x / lambda) `*` dfun (fun _ => dunit false)) 
             (fun (tfF : _*_) (x : X) => if bf x then tfF.`1 x else tfF.`2 x)); last first.
rewrite dfun_dcondE /=.
+ by apply dbiased_ll.
+ by move => *;apply dbiased_ll.
+ by apply dunit_ll.
rewrite /dfun_biased; do 2!congr =>/=.
apply fun_ext => x. 
apply eq_distr => b.
rewrite !dbiased1E /= !clamp_id ; 1, 2: by smt().
rewrite dadd1E /=.
+ rewrite !weight_dscalar ?dbiased_ll ?dunit_ll; smt().
rewrite !dscalar1E. 
+ rewrite ?dbiased_ll ?dunit_ll; smt().
  split; 1: smt().
  by move => *; rewrite dunit_ll /=; smt().

by case b; move => * /=; rewrite dunit1E /= dbiased1E /=; rewrite clamp_id;move :(Hx x);smt().

apply eq_dlet => // hr;rewrite dmap_dprodE /=.
apply eq_dlet => // hp;apply eq_distr => x /=.
rewrite dmap1E /=  /(\o) /pred1 /=.
have -> : (dfun (fun (_ : X) => dunit false)) = 
          dunit (fun x => false); last by rewrite !dunitE; congr =>/= /#.
apply eq_distr => hh;rewrite dunit1E /=.
have -> : pred1 hh = (fun (f : X -> bool) => forall (x : X), (fun xx fxx => hh xx = fxx) x (f x)) by smt().
rewrite dfunE /=.
have -> : (fun (x0 : X) => mu (dunit false) (fun (fxx : bool) => hh x0 = fxx)) = (fun x =>  b2r (!hh x)) by apply fun_ext => x0 /=; rewrite dunitE /#. 
case ((fun (_ : X) => false) = hh).
+ by rewrite fun_ext => H; apply StdBigop.Bigreal.BRM.big1_seq; smt().
by rewrite fun_ext => H; apply StdBigop.Bigreal.prodr_eq0;smt( FinT.enumP). 
qed.

lemma hard_hop _ps _lambda :
  0%r < _lambda < 1%r  => 
   (forall x, 0%r <= _ps x <= _lambda) =>
    equiv [ MixLambda.left ~ MixLambda.right :  lambda{2} = _lambda /\ ps{1} = _ps  /\ ps{2} = _ps ==> ={res} ].
move => lambda_01 Hps.
proc; rnd : *0 *0;auto => />;rewrite distr_equality ?dmap_id //#.
qed.

end MixLambdaDFun.


(***************************************************************************) 
(* Helper theory for doing an easier reprogramming case where only one 
position in a random function gets replaced with a fresh uniformly random 
value *)
(***************************************************************************)


abstract theory PointResampling.

type X.
type Y.

clone import MUniFinFun as MUFF with
  type t <- X.   (* This assumes that the type of from is finite *)

clone import MUniFinFun as MUFFY with
  type t <- Y.

op [lossless uniform full]dx : X distr.
op [lossless uniform full]dy : Y distr.
op dh = MUFF.dfun (fun _ => dy).

axiom Ynontriv: 1 < MUFFY.FinT.card. 

(* At some point should come from SL *)
lemma my_fin_finite (p : Y -> bool) : Finite.is_finite p.
proof.
exists (filter p FinT.enum); split.
- by apply/filter_uniq/FinT.enum_uniq.
- by move=>x; rewrite mem_filter FinT.enumP.
qed.

lemma perm_eq_to_seq_enum : perm_eq FinT.enum (Finite.to_seq predT).
proof.
apply: uniq_perm_eq.
- by apply: FinT.enum_uniq.
- by apply/Finite.uniq_to_seq/my_fin_finite.
- by move=> x; rewrite Finite.mem_to_seq 1:&(my_fin_finite)FinT.enumP.
qed.

lemma L : FinT.card = size (Finite.to_seq<:Y> predT).
proof. by apply/perm_eq_size/perm_eq_to_seq_enum. qed.
(********)

lemma YnontrivS : 
  1 < size ((Finite.to_seq (support dy))).
rewrite /dy; move : Ynontriv; rewrite L.
have -> : support dy = predT; last by done.
rewrite /predT /= /support fun_ext => x.
by rewrite witness_support /= eqT; exists x; rewrite dy_fu /= /pred1 /=. 
qed.

op eps_x =  1%r / (size ((Finite.to_seq (support dx))))%r.
op eps_y =  1%r / (size ((Finite.to_seq (support dy))))%r.

import MUFF.

module PointRS = {
   var h,f : X -> Y
(*   var xstar : X *)
   var y0 : Y
   var dh': (X -> Y) distr

   proc left() = {
       h <$ dh;
   }

   proc right_nice(xstar : X) = {
      (* xstar <$ dx; *)
      dh' <- dmap (dh `*` ((fun (x:X) => dy) xstar))
        (fun (p : (X -> Y) * Y) (x' : X) => if xstar = x' then p.`2 else p.`1 x');
      h <$ dh';
   }

   proc right_prod(xstar: X) = {
      (* xstar <$ dx; *)      
      h <$ dmap (dh `*` dy) (fun (fy : (_*_)) => (fun x =>  if x = xstar then fy.`2 else fy.`1 x));
   }

   proc right_1(xstar : X) = {
       (* xstar <$ dx; *)
       (f,y0) <$ (dh `*` dy);                                         
       h  <-  fun x => if x = xstar then y0 else f x;
   } 

   proc right(xstar : X) = {
       (* xstar <$ dx; *)
       y0 <$ dy;                                         
       f <$ dh;
       h  <-  fun x => if x = xstar then y0 else f x;
   } 

}.

equiv main_theorem : PointRS.left ~ PointRS.right :  true ==> ={PointRS.h}.
proof.
  proc; rnd: *0 *0; skip => /> &2.
  have -> : (dmap dh (fun (h : X -> Y) => h)) = dh.
  + by apply (dmap_bij _ _ _ (fun h => h)).
  rewrite /dmap /(\o) dlet_swap /=.
  have -> : 
    dlet dh
     (fun (x2 : X -> Y) =>
        dlet dy
          (fun (x1 : Y) =>
             dunit (fun (x : X) => if x = xstar{2} then x1 else x2 x))) =
   dmap (dfun (fun (_ : X) => dy) `*` dy)
     (fun (p : (X -> Y) * Y) (x' : X) =>
        if xstar{2} = x' then p.`2 else p.`1 x').
  + rewrite dmap_dprodE; apply in_eq_dlet => //= f hf.
    rewrite /dmap //; apply in_eq_dlet => //= y hy.
    rewrite /(\o); congr; apply fun_ext => x.
    by rewrite (eq_sym x).
  have /= <- // := dfun_dmap_up (fun _ => dy) xstar{2}; apply dy_ll.
qed.

(* End Indirect proof *)
end PointResampling.

(****************   
Helper theory for proving that the constructed function is a random function 
********************)
abstract theory LambdaReprogram.

type X.
type Y.

clone import MUniFinFun as MUFF with
  type t <- X.

clone import MUniFinFun as MUFFY with
  type t <- Y.

op [lossless uniform full]dx : X distr.
op [lossless uniform full]dy : Y distr.
op dh = MUFF.dfun (fun _ => dy).

axiom Ynontriv: 1 < MUFFY.FinT.card. 

(* At some point should come from SL *)
lemma my_fin_finite (p : Y -> bool) : Finite.is_finite p.
proof.
exists (filter p FinT.enum); split.
- by apply/filter_uniq/FinT.enum_uniq.
- by move=>x; rewrite mem_filter FinT.enumP.
qed.

lemma perm_eq_to_seq_enum : perm_eq FinT.enum (Finite.to_seq predT).
proof.
apply: uniq_perm_eq.
- by apply: FinT.enum_uniq.
- by apply/Finite.uniq_to_seq/my_fin_finite.
- by move=> x; rewrite Finite.mem_to_seq 1:&(my_fin_finite)FinT.enumP.
qed.

lemma L : FinT.card = size (Finite.to_seq<:Y> predT).
proof. by apply/perm_eq_size/perm_eq_to_seq_enum. qed.
(********)

lemma YnontrivS : 
  1 < size ((Finite.to_seq (support dy))).
rewrite /dy; move : Ynontriv; rewrite L.
have -> : support dy = predT; last by done.
rewrite /predT /= /support fun_ext => x.
by rewrite witness_support /= eqT; exists x; rewrite dy_fu /= /pred1 /=. 
qed.

op eps_x =  1%r / (size ((Finite.to_seq (support dx))))%r.
op eps_y =  1%r / (size ((Finite.to_seq (support dy))))%r.

op lambda : { real | 0%r < lambda < 1%r } as lambda_bound.


clone import FixedBiased with
     op p <- lambda
     proof in01_p by apply lambda_bound.

op dboolf = MUFF.dfun (fun _ => dbiased).

import MUFF.

module LambdaRepro = {
   proc left() : (X -> Y) = {
       var h;
       h <$ dh;
       return h;
   }

   proc right(xstar : X) : (X -> Y) = {
       var ystar,bf,gy,h;
       ystar <$ dy;                                         
       bf <$ dboolf;                                         
       gy <$ dfun (fun (_ : X) => dy \ pred1 ystar);
       h  <-  fun x => if ! bf x /\ x <> xstar then gy x else ystar;
       return h;
   } 

   (* equal to right modulo the product *)
   proc right_tuple1(xstar : X) : (X -> Y) = {
       var ystar,bf,gy,h;
       ystar <$ dy;
       (gy,bf) <$ (dfun (fun (_ : X) => dy \ pred1 ystar) `*` dboolf);
       h  <-  fun x => if ! bf x /\ x <> xstar then gy x else ystar;
       return h;
   }

   (* equal to tuple1 using DMAPSampling *)
   proc right_tuple2(xstar : X) : (X -> Y) = {
       var ystar,h;
       ystar <$ dy;
       h <$ dmap (dfun (fun (_ : X) => dy \ pred1 ystar) `*` dboolf)
               (fun (gybf : (_*_)) =>  (fun x => if ! gybf.`2 x /\ x <> xstar then gybf.`1 x else ystar));
      return h;
   }

   (* Provable using dlet_dfun? equiv to nice *)
   proc right_nice(xstar : X) : (X -> Y) = {
       var h;
       h <$ dlet dy 
         (fun ystar =>
           dmap (dfun (fun (_ : X) => dy \ pred1 ystar) `*` dboolf)
               (fun (gybf : (_*_)) =>  (fun x => if ! gybf.`2 x /\ x <> xstar then gybf.`1 x else ystar)));
       return h;
   }

}.

import RealSeries RField.

lemma weigh_sumY f : sum (fun (a : Y) => mu1 dy a * f a) = eps_y * sum (fun (a : Y) => f a).
proof. 
have -> : (fun (a : Y) => mu1 dy a * f a) = (fun (a : Y) => eps_y * f a); last by rewrite sumZ.
by apply fun_ext => a; rewrite /dy (mu1_uni_ll _ _ dy_uni dy_ll) /eps_x dy_fu /=.  
qed.

lemma yprob_lt1 y : mu1 dy y < 1%r.
rewrite /dy. 
have H : exists y0, y0 <> y /\ y0 \in dy.
exists (head witness (rem y MUFFY.FinT.enum)). 
+ rewrite dy_fu //=. 
  move :  (rem_filter y MUFFY.FinT.enum MUFFY.FinT.enum_uniq).
  move : (size_rem y MUFFY.FinT.enum (MUFFY.FinT.enumP y)).
  move : Ynontriv; rewrite /card.
  move =>  H H0 H1.
  move : (mem_filter (predC1 y) (head witness (rem y MUFFY.FinT.enum)) MUFFY.FinT.enum ).
  rewrite /predC1 /=. rewrite MUFFY.FinT.enumP /= => <-.
  rewrite -H1 mem_rem_neq.  move : ( head_behead (rem y MUFFY.FinT.enum) witness _).
  + by rewrite -size_eq0; smt(size_rem). 
  have ? : head witness (rem y MUFFY.FinT.enum) \in rem y MUFFY.FinT.enum.
   by rewrite (rem_filter _ _ MUFFY.FinT.enum_uniq) /predC1 /=; smt(mem_head_behead). 
  have ? : ! (y \in rem y MUFFY.FinT.enum).
  + by rewrite (rem_filter _ _ MUFFY.FinT.enum_uniq) /predC1 /=; smt(mem_filter).
  by smt().
  by smt().

elim H => y0 [HY HY0]. 
case (mu1 dy y = 1%r); last by smt(le1_mu).
move => HY1; rewrite HY1 /=.
move : (rnd_funi dy _ y y0); 1: by apply (is_full_funiform _ dy_fu dy_uni).
by smt(@Distr).
qed.

import StdBigop.Bigreal.BRA Finite.

(* Add to lib ??? 

lemma dadd_weight (d1 d2 : 'a distr) :
    weight d1 + weight d2 <= 1%r => weight (d1 + d2) = weight d1 + weight d2.


*)

lemma needed (df1 df2 :  (X -> Y) distr)  :
         (forall x, dmap df1 (fun h => h x) =
                   dmap df2 (fun h => h x)) => df1 = df2.
admitted.
(************************** hard equiv **********************)
lemma equal_distrs _xstar:
    lambda = eps_y =>
  (dlet dy
        (fun (ystar0 : Y) =>
           dlet dboolf
             (fun (bf0 : X -> bool) =>
                dmap (dfun (fun (_ : X) => dy \ pred1 ystar0))
                  (fun (gy0 : X -> Y) (x : X) => 
                     if ! bf0 x /\ x <> _xstar then gy0 x else ystar0))) =
    (dmap dh (fun (h0 : X -> Y) => h0))).

move => ly.
rewrite -/idfun dmap_id /dh.
apply  needed => x. 
apply eq_distr => y. 
admitted.


lemma left_right : 
    lambda = eps_y =>
    equiv [ LambdaRepro.left ~ LambdaRepro.right : true ==> ={res} ].
move => lambdav.
proc;rnd : *0 *0; auto => />. 
by move => &2;rewrite equal_distrs /= /#.
qed.

(* 
print sumr_const.
print big_const.

+ apply fun_ext => ystar. congr. apply fun_ext => bf0. rewrite dfun_dmap.

rewrite -dfunE_dlet_fix1.
*)
lemma left_right_nice : 
    lambda = eps_y =>
    equiv [ LambdaRepro.left ~ LambdaRepro.right_nice : true ==> ={res} ].
move => lambdav.
bypr (res{1}) (res{2}) => //.
move => &1 &2 h.
have -> : 
  Pr[LambdaRepro.left() @ &1 : res = h] = eps_y^(MUFF.FinT.card).
+ byphoare => //. 
  proc. rnd. auto => />. rewrite /dh /dfhash.
  move : (dfun_allE (eps_y) ((fun (_ : X) => dy)) predT pred0  (fun x y => y = h x) _ _ _).
  + by move => x /=;  apply dy_ll.
  + move => x /=; rewrite /eps_y (mu1_uni_ll _ _ dy_uni dy_ll) /=.
    by have -> /= : h x \in dy by apply dy_fu.
  + by auto. 
  rewrite count_pred0 /= Real.RField.expr0 /= /pred0 /predT /=.
  have -> : count (fun (_ : X) => true) FinT.enum = FinT.card; last first.
  + by move => <-; congr; apply fun_ext => hp; rewrite fun_ext. 
  by rewrite count_predT /FinT.card.

byphoare => //.
proc. rnd; auto => /> &hr. 
rewrite dlet1E weigh_sumY /=.
(* probability is 0 for all y except h xstar *)
have -> : 
  sum
  (fun (a : Y) =>
     mu1
       (dmap (dfun (fun (_ : X) => dy \ pred1 a) `*` dboolf)
          (fun (gybf : (X -> Y) * (X -> bool)) (x : X) => if ! gybf.`2 x /\ x <> xstar{hr} then gybf.`1 x else a)) h) = 
mu1
       (dmap (dfun (fun (_ : X) => dy \ pred1 (h xstar{hr})) `*` dboolf)
          (fun (gybf : (X -> Y) * (X -> bool)) (x : X) => if ! gybf.`2 x /\ x <> xstar{hr} then gybf.`1 x else (h xstar{hr}))) h.
+ rewrite (sumE_fin _ (MUFFY.FinT.enum) (MUFFY.FinT.enum_uniq)) => /=.
  move => y0; rewrite MUFFY.FinT.enumP //=.
  rewrite (StdBigop.Bigreal.BRA.bigEM (pred1 (h xstar{hr}))) /=. 
  have -> /=:  StdBigop.Bigreal.BRA.big (predC (pred1 (h xstar{hr})))
    (fun (a : Y) =>
      mu1
        (dmap (dfun (fun (_ : X) => dy \ pred1 a) `*` dboolf)
           (fun (gybf : (X -> Y) * (X -> bool)) (x : X) => if ! gybf.`2 x /\ x <> xstar{hr} then gybf.`1 x else a)) h)
    MUFFY.FinT.enum = 0%r.
  + rewrite StdBigop.Bigreal.BRA.big_mkcond.
    have -> : (fun (i : Y) =>
      if predC (pred1 (h xstar{hr})) i then
        (fun (a : Y) =>
           mu1
             (dmap (dfun (fun (_ : X) => dy \ pred1 a) `*` dboolf)
                (fun (gybf : (X -> Y) * (X -> bool)) (x : X) => if ! gybf.`2 x /\ x <> xstar{hr} then gybf.`1 x else a))
             h) i
      else 0%r) = fun x => 0%r; last by apply StdBigop.Bigreal.BRA.big1_seq.
    apply fun_ext => y0. 
    case (pred1 (h xstar{hr}) y0); 1: by move => ->; rewrite /predC /=.
    move => @/pred1 Hy0 /=.
    rewrite /dy dmap1E /pred1 /= /(\o) /= /predC /= Hy0 /=.
    rewrite (mu_eq_support _ _
       (fun (x :  (X -> Y) * (X -> bool)) => 
           (fun gy => forall x0, (fun xx yy => !(h xx = y0) => yy = h xx) (x0) (gy x0)) x.`1 /\
           (fun bf => forall x0, (fun xx yy => h xx = y0 <=> (yy \/ xx = xstar{hr})) (x0) (bf x0)) x.`2)).
    + move => gybf; rewrite supp_dprod /dboolf !dfun_supp  /= => [#] H1 H2.
      by rewrite eq_iff /=; split; move => *; smt(supp_dexcepted). 
    rewrite dprodE !dfunE /=. 
    have := (StdBigop.Bigreal.prodr_eq0 predT (fun (x : X) => mu dbiased (fun (yy : bool) => h x = y0 <=> yy \/ x = xstar{hr})) FinT.enum) => |> [->] //=. 
    by exists xstar{hr}; rewrite /predT /= FinT.enumP /=; smt(mu0).

  have -> : pred1 (h xstar{hr}) = predI (pred1 (h xstar{hr})) (pred1 (h xstar{hr}))  by rewrite /predI /#.
  rewrite -StdBigop.Bigreal.BRA.big_filter_cond filter_pred1 /= MUFFY.FinT.enum_spec /= nseq1 /=.
  rewrite StdBigop.Bigreal.BRA.big_mkcond StdBigop.Bigreal.BRA.big_seq1 /= {1}/pred1 /=.
  rewrite /predI /= /pred1 /=; congr;congr;congr;congr => /=; rewrite fun_ext => x /=.
  by move => * /=;  congr; smt(). 

    rewrite /dy dmap1E /pred1 /= /(\o) /= /predC /=.
    rewrite (mu_eq_support _ _
       (fun (x :  (X -> Y) * (X -> bool)) => 
           (fun gy => forall x0, (fun xx yy => !(h xx = h xstar{hr}) => yy = h xx) (x0) (gy x0)) x.`1 /\
           (fun bf => forall x0, (fun xx yy => h xx = h xstar{hr} <=> (yy \/ xx = xstar{hr})) (x0) (bf x0)) x.`2)).
    + move => gybf; rewrite supp_dprod /dboolf !dfun_supp  /= => [#] H1 H2.
      by rewrite eq_iff; smt(supp_dexcepted). 
  rewrite dprodE => /=.



  move : (dfun_allE_cond (eps_y/(1%r-eps_y)) (fun (_ : X) => dy \ transpose (=) (h xstar{hr})) (fun x0 => h x0 <> h xstar{hr}) pred0 (fun xx yy => yy = h xx) _ _ _).
  + by move => *; apply dexcepted_ll; [apply dy_ll | rewrite  yprob_lt1 ].
  + move => x /=; rewrite dexceptedE /= /predI /predC/= /pred0 /= => H. 
    have -> : (fun (x0 : Y) => x0 =  h x /\ x0 <> (h xstar{hr})) = pred1 (h x) by smt().
    have -> : (transpose (=) (h xstar {hr})) = pred1 (h xstar{hr}) by smt().
    by rewrite !(mu1_uni _ _ dy_uni) !dy_fu /= !dy_ll /eps_y. 
  + by move => /= x0; by rewrite /pred0 /=.


rewrite /dboolf count_pred0 /= Real.RField.expr0 /= /pred0 /predT /= => ->.

move : (dfun_allE_cond (eps_y) (fun (_ : X) => dbiased) (fun x0 => x0 <> xstar{hr} /\ h x0 = h xstar{hr}) (fun x0 => x0 <> xstar{hr} /\ h x0 <> h xstar{hr}) (fun xx yy => yy) _ _ _) => /=.
+ by move => *; apply dbiased_ll.
+ by move => * /=; rewrite dbiasedE /= lambdav. 
+ by smt().

have -> : (fun (f : X -> bool) =>
     (forall (x : X), x <> xstar{hr} /\ h x = h xstar{hr} => f x) /\
     forall (x : X), x <> xstar{hr} /\ h x <> h xstar{hr} => ! f x) = 
     (fun (bf : X -> bool) => forall (x0 : X), h x0 = h xstar{hr} <=> bf x0 \/ x0 = xstar{hr}) 
  by apply fun_ext => x; smt().

move => ->.

have -> : (fun (x0 : X) => x0 <> xstar{hr} /\ h x0 <> h xstar{hr}) = 
          (fun (x0 : X) => h x0 <> h xstar{hr}) by smt().

pose K := count (fun (x0 : X) => h x0 <> h xstar{hr}) FinT.enum.

have -> : count (fun (x0 : X) => x0 <> xstar{hr} /\ h x0 = h xstar{hr}) FinT.enum =
          FinT.card - K - 1. 
+ rewrite /FinT.card -(FinT.count_mem _ FinT.enum_uniq) /= (_: mem FinT.enum = predT);  1: smt(FinT.enumP). 
  rewrite (countID predT (fun x => h x = h xstar{hr})) /predC /predI /predT /= -/K.
  rewrite (countID (fun (x : X) => h x = h xstar{hr}) (fun x => x <>  xstar{hr})) /predC /predI /predT /=.
  have -> : (fun (x : X) => h x = h xstar{hr} /\ x = xstar{hr}) = pred1 xstar{hr} by smt().
  rewrite FinT.enum_spec /= -!Ring.IntID.addrA (_: 1 + (K + ((-K) - 1)) = 0) /=; 1: by ring.
  by congr; smt().

rewrite mulrA mulrC mulrA !expfM /= !expr1z /= -/eps_y. 
have -> : eps_y ^ (FinT.card - K - 1) * (1%r - eps_y) ^ K * eps_y * (eps_y ^ K * inv (1%r - eps_y) ^ K) = 
          (eps_y ^ (FinT.card - K - 1) * eps_y * eps_y ^ K) * ((1%r - eps_y) ^ K * inv (1%r - eps_y) ^ K) by ring.
rewrite -{2}(expr1 eps_y). 
rewrite  -!StdOrder.RealOrder.Domain.exprD /eps_y /=; 1,2: by smt(StdOrder.RealOrder.invr_lt0 YnontrivS). 
rewrite -expfM divrr /=; 1: by smt(StdOrder.RealOrder.invr_lt0 YnontrivS). 

by rewrite StdOrder.RealOrder.Domain.expr1z /= /#.


qed.

require import DProd.
clone import DLetSampling with
    type t <- Y,
    type u <- (X -> Y).

equiv nice_sampledlet _x :
   LambdaRepro.right_nice ~ SampleDLet.sample : 
    xstar{1} = _x /\ dt{2} = dy /\
    du{2} = (fun y0 =>
           dmap (dfun (fun (_ : X) => dy \ pred1 y0) `*` dboolf)
               (fun (gybf : (_*_)) =>  (fun x => if ! gybf.`2 x /\ x <> _x then gybf.`1 x else y0)))  
             ==> res{1} = res{2} by proc; auto => />.

equiv tuple2dep _x :
   LambdaRepro.right_tuple2 ~ SampleDep.sample : 
    xstar{1} = _x /\ dt{2} = dy /\
    du{2} = (fun y0 =>
           dmap (dfun (fun (_ : X) => dy \ pred1 y0) `*` dboolf)
               (fun (gybf : (_*_)) =>  (fun x => if ! gybf.`2 x /\ x <> _x then gybf.`1 x else y0)))  
             ==> res{1} = res{2} by proc; auto => />.

equiv nice_tuple2 _x :
   LambdaRepro.right_nice ~ LambdaRepro.right_tuple2 : 
      xstar{1} = _x /\ xstar{2} = _x ==> ={res}.
proc*.
transitivity {1} { r <@ SampleDLet.sample(dy,
        ((fun y0 =>
           dmap (dfun (fun (_ : X) => dy \ pred1 y0) `*` dboolf)
               (fun (gybf : (_*_)) =>  (fun x => if ! gybf.`2 x /\ x <> _x then gybf.`1 x else y0))))); }
        (xstar{1} = _x /\ xstar{2} = _x ==> ={r}) 
        (xstar{1} = _x /\ xstar{2} = _x  ==> ={r}); 1,2: by smt().
+ by ecall (nice_sampledlet xstar{1}) => />.

transitivity {1} {r <@ SampleDep.sample(dy,
        ((fun y0 =>
           dmap (dfun (fun (_ : X) => dy \ pred1 y0) `*` dboolf)
               (fun (gybf : (_*_)) =>  (fun x => if ! gybf.`2 x /\ x <> _x then gybf.`1 x else y0))))); }
        (xstar{1} = _x /\ xstar{2} = _x ==> ={r}) 
        (xstar{1} = _x /\ xstar{2} = _x  ==> ={r}); 1,2: by smt().
by symmetry; ecall (SampleDepDLet) => />.

by symmetry;ecall (tuple2dep xstar{1}) => />.

qed.

require import DMap.
clone import DMapSampling with
    type t1 <- (X -> Y) * (X -> bool),
    type t2 <- (X -> Y).

require import DProd.
clone import ProdSampling with
    type t1 <- X -> Y,
    type t2 <- X -> bool.

equiv tuple2tuple1 _x :
   LambdaRepro.right_tuple2 ~ LambdaRepro.right_tuple1 : xstar{1} = _x /\ xstar{2} = _x==> ={res}. 
proc. seq 1 1 : (#pre /\ ={ystar}); 1: by auto.
transitivity {1} { h <@ DMapSampling.S.sample((dfun (fun (_ : X) => dy \ pred1 ystar) `*` dboolf),
                      (fun (gybf : (X -> Y) * (X -> bool)) (x : X) => 
                       if ! gybf.`2 x /\ x <> xstar then gybf.`1 x else ystar));} (={ystar,xstar} ==> ={h})(={ystar,xstar} ==> ={h}); 1,2: smt().
+ by inline *;auto =>/>. 

transitivity {1} { h <@ DMapSampling.S.map((dfun (fun (_ : X) => dy \ pred1 ystar) `*` dboolf),
                      (fun (gybf : (X -> Y) * (X -> bool)) (x : X) => 
                       if ! gybf.`2 x /\ x <> xstar then gybf.`1 x else ystar));} (={ystar,xstar} ==> ={h})(={ystar,xstar} ==> ={h}); [ by smt() | by smt() | | by inline *;auto =>/>]. 

by call(DMapSampling.sample).

qed.

equiv tuple1right _x :
   LambdaRepro.right_tuple1 ~ LambdaRepro.right : xstar{1} = _x /\ xstar{2} = _x==> ={res}. 
proc. wp;seq 1 1 : (={xstar,ystar}); 1: by auto.
transitivity {1} { (gy,bf) <@ ProdSampling.S.sample(dfun (fun (_ : X) => dy \ pred1 ystar), dboolf);} (={ystar,xstar} ==> ={xstar,ystar,gy,bf})(={ystar,xstar} ==> ={xstar,ystar,gy,bf}); 1,2: smt().
+ by inline *;auto =>/>. 

swap {2} 1 1 .
transitivity {2} { (gy,bf) <@ ProdSampling.S.sample2(dfun (fun (_ : X) => dy \ pred1 ystar), dboolf);} (={ystar,xstar} ==> ={xstar,ystar,gy,bf})(={ystar,xstar} ==> ={xstar,ystar,gy,bf}); [ by smt() | by smt() | | by inline *;auto =>/>]. 

by call(ProdSampling.sample_sample2).

qed.

lemma main_theorem _x : 
    lambda = eps_y =>
    equiv [ LambdaRepro.left ~ LambdaRepro.right : xstar{2} = _x ==> ={res} ].
move => Hl.

proc*.

transitivity {1} {r <@ LambdaRepro.right_nice(_x);}
            (true ==> ={r}) (xstar{2} = _x ==> ={r}); 1,2: by smt(). 
+ by call left_right_nice => //.

transitivity {1} {r <@ LambdaRepro.right_tuple2(_x);}
            (true ==> ={r}) 
             (xstar{2} = _x  ==> ={r}); 1,2: by smt(). 
+ by call (nice_tuple2 _x) => //.

transitivity {1} {r <@ LambdaRepro.right_tuple1(_x);}
            (true ==> ={r}) 
             (xstar{2} = _x  ==> ={r}); 1,2: by smt(). 
+ by call (tuple2tuple1 _x) => //.

by call (tuple1right _x).
qed.

end LambdaReprogram.

