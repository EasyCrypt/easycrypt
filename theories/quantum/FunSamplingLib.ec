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

op [lossless] dy : Y distr.
op dh = MUFF.dfun (fun _ => dy).

import MUFF.

module PointRS = {
   var h,f : X -> Y
(*   var xstar : X *)
   var y0 : Y
   var dh': (X -> Y) distr

   proc left() = {
       h <$ dh;
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

end PointResampling.

(****************   
Helper theory for proving that the constructed function is a random function 
********************)
abstract theory LambdaReprogram.


type X.
type Y.

clone import MUniFinFun as MUFF with
  type t <- X.

(*
clone import MFinite as MFX with 
  type t <- X,
  theory Support <- MUFF.FinT.

abbrev dx = MFX.dunifin.

*)



(* ? Why we do not define those operators ?  *)
(* op [lossless uniform full]dx : X distr. *)

clone import MFinite as MFY 
  with type t <- Y.

abbrev dy = MFY.dunifin.

axiom Ynontriv: 1 < MFY.Support.card. 

op dh = MUFF.dfun (fun _ => dy).

op lambda =  1%r / MFY.Support.card%r.

lemma lambda_bound : 0%r < lambda < 1%r.
proof. smt(MFY.Support.card_gt0 Ynontriv). qed.

clone import FixedBiased with
  op p <- lambda
  proof in01_p by apply lambda_bound.

op dboolf = MUFF.dfun (fun _ => dbiased).

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
}.

import RealSeries RField.

lemma yprob_lt1 y : mu1 dy y < 1%r.
proof. by rewrite dunifin1E; case lambda_bound. qed.

(************************** hard equiv **********************)

lemma equal_distrs _xstar:
  (dlet dy
        (fun (ystar0 : Y) =>
           dlet dboolf
             (fun (bf0 : X -> bool) =>
                dmap (dfun (fun (_ : X) => dy \ pred1 ystar0))
                  (fun (gy0 : X -> Y) (x : X) => if ! bf0 x /\ x <> _xstar then gy0 x else ystar0))) =
    (dmap dh (fun (h0 : X -> Y) => h0))).
proof.
rewrite dmap_id.
rewrite /dh /dfhash (dfun_dmap_up _ _xstar).
+ by apply dunifin_ll.
rewrite dmap_dprodE_swap.
apply eq_dlet => // ystar.
have -> : (fun (bf0 : X -> bool) =>
   dmap (dfun (fun (_ : X) => dy \ pred1 ystar))
     (fun (gy0 : X -> Y) (x : X) =>
        if ! bf0 x /\ x <> _xstar then gy0 x else ystar)) = 
  (fun (bf0 : X -> bool) =>
     dfun (fun x => dmap (dy \ pred1 ystar) (fun fx => if ! bf0 x /\ x <> _xstar then fx else ystar))).
+ by apply fun_ext => bf; rewrite -dmap_dfun.
rewrite /dboolf.
rewrite (dlet_dfun _ (fun x b => dmap (dy \ pred1 ystar) (fun (fx : Y) => if !b /\ x <> _xstar then fx else ystar))) /=.
rewrite (dmap_dfun _ (fun x' fx => if _xstar = x' then ystar else fx)).
congr; apply fun_ext => x /=.
rewrite (eq_sym x).
case (_xstar = x) => /= [<<- | ?].
+ rewrite dmap_cst. 
  + by apply dexcepted_ll;[apply/dunifin_ll | apply/yprob_lt1].
  by rewrite dlet_cst ?dbiased_ll dmap_cst ?dunifin_ll.
have -> : 
   (fun (b : bool) =>
      dmap (dy \ pred1 ystar) (fun (fx : Y) => if !b then fx else ystar)) = 
   (fun (b : bool) =>
      dmap (dy \ pred1 ystar) (fun (fx : Y) => if b then ystar else fx)).
+ by apply fun_ext => -[].
rewrite dmap_id.
apply eq_distr => y. 
rewrite dlet1E /= (sumE_fin _ [true; false]) //; 1: by case.
rewrite !big_cons big_nil /predT /= dmap_id dmap_cst.
+ by apply dexcepted_ll; [apply dunifin_ll | apply yprob_lt1].
rewrite dexcepted1E !dbiased1E /= /lambda dunitE.
rewrite !dunifin1E dunifin_ll /pred1 (eq_sym ystar); case (y = ystar) => //= _.
field; smt(Ynontriv).
qed.

lemma main_theorem : 
  equiv [ LambdaRepro.left ~ LambdaRepro.right : true ==> ={res} ].
proof.
proc;rnd : *0 *0; auto => />. 
by move => &2;rewrite equal_distrs /= /#.
qed.

end LambdaReprogram.

