(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore List FSet Distr DProd DList StdBigop StdOrder RealFLub.
require import Hybrid.
(*---*) import Bigreal RealSeries RealOrder RField BRA MRat.

require PROM.

(********** statistical distance ***************************************)

(* This file defines the notion of statistical distance for
(sub)distributions: 

  sdist d1 d2 = lub_E ( |mu d1 E - mu d2 E| )

Note that for subdistributions, this definition is not equivalent to
the usual total variation distance (1/2 * sum_x | mu1 d1 x - mu d2 x |). 
To see this, consider [d1 = dunit tt] and [d2 = drat []]. The correct 
equivalence is given by:

  sdist d1 d2 = 1/2 * (|weight d1 - weight d2| + sum_x | mu1 d1 x - mu d2 x |)

(see [sdist_tvd below). *)

op sdist (d1 d2 : 'a distr) = flub (fun E => `|mu d1 E - mu d2 E|).

lemma sdist_upper_bound (d1 d2 : 'a distr) E : 
  `|mu d1 E - mu d2 E| <= sdist d1 d2.
proof.
apply (flub_upper_bound 1%r (fun E => `|mu d1 E - mu d2 E|)).
move => {E} E /=; smt(mu_bounded).
qed.
 
lemma sdist_le_ub (d1 d2 : 'a distr) r :
  (forall E, `|mu d1 E - mu d2 E| <= r) => sdist d1 d2 <= r .
proof. exact flub_le_ub. qed.

(*-- sdist is a metric -------------------------------------------------------*)

lemma sdist_ge0 (d1 d2 : 'a distr) : 0%r <= sdist d1 d2.
proof. 
have -> : 0%r = `|mu d1 pred0 - mu d2 pred0| by rewrite !mu0.
exact sdist_upper_bound.
qed.

lemma sdistdd (d : 'a distr) : sdist d d = 0%r.
proof. 
apply ler_anti; rewrite sdist_ge0 /=. 
by apply sdist_le_ub => E; rewrite subrr.
qed.

lemma sdist_triangle (d2 d1 d3 : 'a distr) : 
  sdist d1 d3 <= sdist d1 d2 + sdist d2 d3.
proof.
apply sdist_le_ub => E.
apply (ler_trans (`| mu d1 E - mu d2 E | + `| mu d2 E - mu d3 E |)).
  smt(mu_bounded).
by rewrite ler_add; apply/sdist_upper_bound.
qed.

lemma sdist0_eq (d1 d2 : 'a distr) : sdist d1 d2 = 0%r => d1 = d2.
proof.
suff S: d1 <> d2 => 0%r < sdist d1 d2 by apply contraLR; smt(sdist_ge0). 
apply: distrW d2 => m2 isd2 /=; apply: distrW d1 => m1 isd1 /= H.
have {H} [x Dx] : exists x, m1 x <> m2 x. 
  by apply: contraLR H => ?; rewrite negbK; congr; smt().
apply (ltr_le_trans `|mu1 (mk m1) x - mu1 (mk m2) x|); last exact sdist_upper_bound.
by rewrite !muK // /#.
qed.

lemma sdistC (d1 d2 : 'a distr) : sdist d1 d2 = sdist d2 d1.
proof.
suff S : forall (d1 d2 : 'a distr), sdist d1 d2 <= sdist d2 d1.
  by apply/ler_anti; split => [|_]; exact S.
move => {d1 d2} d1 d2; apply sdist_le_ub => E. 
by rewrite distrC sdist_upper_bound.
qed.

(*----------------------------------------------------------------------------*)

lemma sdist_dmap (d1 d2 : 'a distr) (F : 'a -> 'b) : 
  sdist (dmap d1 F) (dmap d2 F) <= sdist d1 d2.
proof. by apply sdist_le_ub => E; rewrite !dmapE; exact sdist_upper_bound. qed.

(*----------------------------------------------------------------------------*)

lemma summable_sdist (d1 d2 : 'a distr) : 
  summable (fun x => `| mu1 d1 x - mu1 d2 x |).
proof. 
apply/summable_norm/summableD; 1: exact/summable_mu1. 
exact/summableN/summable_mu1.
qed.

lemma sdist_tvd (d1 d2 : 'a distr) : 
  sdist d1 d2 = 
  1%r/2%r * (sum (fun x => `| mu1 d1 x - mu1 d2 x |) + `|weight d1 - weight d2|).
proof.
wlog : d1 d2 / 
  sum (fun x => if ! mu1 d1 x >= mu1 d2 x then `|mu1 d1 x - mu1 d2 x| else 0%r) <= 
  sum (fun x => if mu1 d1 x >= mu1 d2 x then `|mu1 d1 x - mu1 d2 x| else 0%r).
+ move => W; have := W d1 d2; have {W} := W d2 d1.
  pose Sp (d1 d2 : 'a distr) := 
    sum (fun x => if mu1 d1 x >= mu1 d2 x then `|mu1 d1 x - mu1 d2 x| else 0%r).
  pose Sn (d1 d2 : 'a distr) := 
    sum (fun x => if ! mu1 d1 x >= mu1 d2 x then `|mu1 d1 x - mu1 d2 x| else 0%r). 
  rewrite -/(Sp d1 d2) -/(Sp d2 d1) -/(Sn d1 d2) -/(Sn d2 d1) => W2 W1.
  case: (Sn d1 d2 <= Sp d1 d2) => [|H]; 1: exact W1. 
  rewrite sdistC distrC (eq_sum _ (fun (x : 'a) => `|mu1 d2 x - mu1 d1 x|)).
    by move => x /=; rewrite distrC. 
  apply: W2; move: H; rewrite -ltrNge => {W1 W2} /ltrW H. 
  suff S : forall d1 d2, Sn d2 d1 = Sp d1 d2 by rewrite S -(S d2 d1).
  by move => d1' d2'; apply/eq_sum => x /=; smt().  
pose F E := `|mu d1 E - mu d2 E|; pose f x := `|mu1 d1 x - mu1 d2 x|.
have sum_f : summable f by apply summable_sdist.
pose pos x := mu1 d1 x >= mu1 d2 x.
pose Sp := sum (fun x => if pos x then f x else 0%r).
pose Sn := sum (fun x => if !pos x then f x else 0%r).
move => tmp; have {tmp} ler_Sn_Sp : Sn <= Sp by done.
rewrite (sum_split _ pos) // -/Sp -/Sn.
have <- : `| Sp - Sn | = `|weight d1 - weight d2|.
  rewrite /Sp /Sn -sumB /=; try exact/summable_cond/summable_sdist.
  rewrite !weightE -sumB /= ?summable_mu1. 
  by congr; apply eq_sum => x /= /#.
suff : flub F = Sp by rewrite /sdist -/F; smt(ler_def).
apply ler_anti; split => [|_]; last first. 
- apply (ler_trans (F pos)); 2: by apply (flub_upper_bound 1%r); smt(mu_bounded).
  rewrite /Sp /F /f !muE -sumB /=; 1,2: exact summable_mu1_cond.
  apply (ler_trans _ _ _ _ (ler_norm _)). 
  apply ler_sum;  [smt()|apply/summable_cond/summable_sdist|].
  by apply/summableD;[|apply/summableN]; apply/summable_mu1_cond.
apply sdist_le_ub => E.
rewrite (mu_split d1 E pos) (mu_split d2 E pos). 
have -> : forall (a b c d : real), a + b - (c + d) = (a - c) + (b - d) by smt().
rewrite !muE -!sumB /=; 1..4: exact: summable_mu1_cond.
rewrite (eq_sum _ 
  (fun x => if predI E pos x then mu1 d1 x - mu1 d2 x else 0%r)); 1: smt().
rewrite (eq_sum 
  (fun (x : 'a) => (if predI E (predC pos) x then mu1 d1 x else 0%r) - 
                    if predI E (predC pos) x then mu1 d2 x else 0%r)
  (fun x => if predI E (predC pos) x then mu1 d1 x - mu1 d2 x else 0%r)); 1: smt().
pose SEp := sum (fun (x : 'a) => 
                 if predI E pos x then mu1 d1 x - mu1 d2 x else 0%r).
pose SEn := sum (fun (x : 'a) => 
                 if predI E (predC pos) x then mu1 d1 x - mu1 d2 x else 0%r).
have ? : 0%r <= SEp /\ SEn <= 0%r. 
  split; [apply ge0_sum| apply le0_sum => x /= @/predI @/predC @/pos]; smt().
suff : maxr SEp (-SEn) <= Sp by smt().
apply/ler_maxrP; split. 
- (apply ler_sum; 1: smt()); 2: exact/summable_cond.
  exact/summable_cond/norm_summable/summable_sdist.
- apply: ler_trans ler_Sn_Sp; 
    rewrite -sumN; (apply ler_sum; 1: smt()); 2: exact/summable_cond.
  exact/summableN/summable_cond/norm_summable/summable_sdist.
qed.

(*----------------------------------------------------------------------------*)

lemma sdist_dlet (d1 d2 : 'a distr) (F : 'a -> 'b distr) : 
   sdist (dlet d1 F) (dlet d2 F) <= sdist d1 d2.
proof. 
apply sdist_le_ub => E; rewrite !dletE sdist_tvd.
rewrite div1r (ler_pdivl_mull 2%r) //.
rewrite -sumB ?summable_mu1_wght /=; 1,2: smt(mu_bounded).
rewrite (eq_sum _ (fun x => (mu1 d1 x - mu1 d2 x) * mu (F x) E)).
  by move => x /= /#.
pose p x := mu1 d2 x <= mu1 d1 x.
have sum_d1d2 : summable (fun x => mu1 d1 x - mu1 d2 x).
  by apply/summableD;[|apply summableN]; apply summable_mu1.
have sum_d1d2E : summable (fun x => (mu1 d1 x - mu1 d2 x) * mu (F x) E).
  by apply (summableM_bound 1%r) => // x; smt(mu_bounded).
rewrite (sum_split _ p) //=. 
pose Sp := sum (fun (x : 'a) => 
           if p x then (mu1 d1 x - mu1 d2 x) * mu (F x) E else 0%r).
pose Sn := sum (fun (x : 'a) => 
           if !p x then (mu1 d1 x - mu1 d2 x) * mu (F x) E else 0%r).
have Sp_ge0 : 0%r <= Sp by apply ge0_sum => /= x;smt(mu_bounded).
have Sn_le0 : Sn <= 0%r by apply le0_sum => /= x;smt(mu_bounded).
case : (`|Sp| >= `|Sn|) => H.
+ apply (ler_trans (2%r*Sp)); 1: smt().
  apply (ler_trans (2%r * sum (fun x => if p x then mu1 d1 x - mu1 d2 x else 0%r))).
    rewrite ler_pmul2l // /Sp &(ler_sum) => [x /=| |]; 2,3: exact summable_cond.
    by case: (p x) => // @/p Hp; apply ler_pimulr; smt(mu_bounded).
  rewrite sum_split_dist /= ?summable_mu1.
  have -> : forall x, 2%r * x = x + x by smt().
  rewrite -addrA &(ler_add) // addrC ler_subr_addl.
  by rewrite -sum_split // sumB ?summable_mu1 -!weightE; smt().
+ apply (ler_trans (2%r* -Sn)) => [|{H}]; 1: smt().
  apply (ler_trans (2%r * - sum (fun x => if !p x then mu1 d1 x - mu1 d2 x else 0%r))).
    rewrite ler_pmul2l // &(ler_opp2) &(ler_sum) => [x /=| |]; 2,3: exact summable_cond.
    by case: (p x) => //= @/p Hp; rewrite &(ler_nimulr); smt(mu_bounded).
  rewrite sum_split_dist /= ?summable_mu1.
  rewrite -[(_ - _)%Real]addrC -addrA. 
  have -> : forall x, 2%r * x = x + x by smt().
  apply ler_add => //. rewrite -ler_subl_addl -opprD -sum_split //. 
  by rewrite sumB ?summable_mu1 -!weightE /#.
qed. 

(*----------------------------------------------------------------------------*)

lemma sdist_dprod2r (d1 d2 : 'a distr) (d : 'b distr) : 
  sdist (d1 `*` d) (d2 `*` d) = sdist d1 d2 * weight d.
proof.
rewrite !sdist_tvd -[1%r/2%r * _ * _]mulrA !weight_dprod; congr.
have -> : forall (a b c : real), (a + b) * c = a * c + b * c by smt().
congr; 2:smt(mu_bounded).
rewrite mulrC -sumZ /= sum_pair; 1: exact summable_sdist.
apply eq_sum => x /=.
rewrite (eq_sum _ (fun b => `|mu1 d1 x - mu1 d2 x| * mu1 d b)) => [b /=|].
+ rewrite !dprod1E; smt(mu_bounded).
by rewrite sumZ mulrC -weightE.
qed.

lemma sdist_dprodC_aux (dl1 dl2 : 'a distr) (dr1 dr2 : 'b distr) :
  sdist (dl1 `*` dr1) (dl2 `*` dr2) <= sdist (dr1 `*` dl1) (dr2 `*` dl2).
proof.
apply sdist_le_ub => E; rewrite (dprodC dl1 dr1) (dprodC dl2 dr2) !dmapE.
exact: sdist_upper_bound.
qed.

lemma sdist_dprodC (dl1 dl2 : 'a distr) (dr1 dr2 : 'b distr) :
  sdist (dl1 `*` dr1) (dl2 `*` dr2) = sdist (dr1 `*` dl1) (dr2 `*` dl2).
proof. by apply ler_anti; rewrite !sdist_dprodC_aux. qed.

lemma sdist_dprod (dl1 dl2 : 'a distr) (dr1 dr2 : 'b distr) :
  sdist (dl1 `*` dr1) (dl2 `*` dr2) <= sdist dl1 dl2 + sdist dr1 dr2.
proof.
have L := sdist_triangle (dl2 `*` dr1) (dl1 `*` dr1) (dl2 `*` dr2).
apply (ler_trans _ _ _ L); rewrite (sdist_dprodC dl2) !sdist_dprod2r //.
rewrite ler_add; smt(mu_bounded sdist_ge0 ler_pimulr).
qed.

lemma sdist_dlist (d1 d2 : 'a distr) n : 
  0 <= n => sdist (dlist d1 n) (dlist d2 n) <= n%r * sdist d1 d2.
proof.
elim: n => [|n ? IHn]; 1: by rewrite !dlist0 // sdistdd.
rewrite !dlistS //. 
apply (ler_trans _ _ _ (sdist_dmap _ _ _)).
apply (ler_trans _ _ _ (sdist_dprod _ _ _ _ )); smt().
qed.

(*----------------------------------------------------------------------------*)

(* Generic Distinguishers and their output distributions *)
abstract theory GenDist.
type in_t, out_t. 

module type Distinguisher = { 
  proc guess (x : in_t) : out_t
}.

lemma uniq_big_res (A <: Distinguisher) &m x' (bs : out_t list) : 
  uniq bs =>
  big predT (fun b => Pr[A.guess(x') @ &m : res = b]) bs = 
  Pr[A.guess(x') @ &m : res \in bs].
proof.
elim: bs => [_|b bs IHbs /= [bNbs uq_bs]].
  by rewrite big_nil; byphoare => //; hoare; auto.
by rewrite big_cons {1}/predT /= IHbs // Pr[mu_disjoint] /#.
qed.

lemma adv_isdistr (A <: Distinguisher) &m x' : 
    isdistr (fun b => Pr[A.guess(x') @ &m : res = b]).
proof.
split => [/= y|bs uq_bs]; 1: by byphoare.
by rewrite (uniq_big_res A &m) //; byphoare. 
qed.

lemma adv_mu1 (A <: Distinguisher) &m z x' : 
  Pr[A.guess(x') @ &m : res = z] = 
  mu1 (mk (fun b => Pr[A.guess(x') @ &m : res = b])) z.
proof.
by rewrite muK //; exact (adv_isdistr A).
qed.

module S = {
  proc sample (d : out_t distr) = {
    var r; 
  
    r <$ d;
    return r;
  }
}.

lemma sampleE d' &m a : 
    Pr[S.sample(d') @ &m : res = a] = mu1 d' a.
proof.
by byphoare (: d = d' ==> _) => //; proc; rnd; auto.
qed.

end GenDist.

(*----------------------------------------------------------------------------*)

(* Boolean distinguishers for distributions *)

abstract theory Dist. 
type a. 

clone import GenDist with
  type in_t <- a,
  type out_t <- bool
  proof*.

clone import DLetSampling as DLS with
  type t <- a,
  type u <- bool
  proof*.

(* Part 1 : Sampling game: the distinguiser is given a sampled value *)

module Sample (A : Distinguisher) = { 
  proc main(d : a distr) = {
    var x,r; 

    x <$ d;
    r <@ A.guess(x);
    return r;
  }
}.

lemma Sample_dlet (A <: Distinguisher) &m d' : 
    Pr [Sample(A).main(d') @ &m : res] = 
    mu1 (dlet d' (fun x => (mk (fun z => Pr [A.guess(x) @ &m : res=z])))) true.
proof. 
pose F := (fun x => (mk (fun r => Pr [A.guess(x) @ &m : res = r]))).
have -> : Pr[Sample(A).main(d') @ &m : res] = 
          Pr[SampleDep.sample(d',F) @ &m : res].
  byequiv => //; proc. 
  seq 1 1 : ((glob A){1} = (glob A){m} /\ du{2} = F /\ x{1} = t{2}). 
    by rnd; skip; smt(). (* rnd; auto raises anomaly *)
  transitivity{2} {u <@ S.sample(du t); } 
    ((glob A){1} = (glob A){m} /\ du{2} = F /\ x{1} = t{2} ==> r{1} = u{2}) 
    (={du,t} ==> ={u}); 1,2: smt(); 2: by inline*;auto.
  call (: d{2} = (F x){1} /\ (glob A){1} = (glob A){m} ==> ={res}).
  bypr (res{1}) (res{2}); 1:smt(). 
  move => &1 &2 a [-> eq_globA]; rewrite sampleE -(adv_mu1 A). 
  byequiv (: ={x,glob A} ==> ={res}) => //; 1: by sim. 
  by move: F => F; auto. (* abstracting over F avoids anomaly *)
have -> : Pr[SampleDep.sample(d', F) @ &m : res] = 
          Pr[SampleDLet.sample(d', F) @ &m : res].
  byequiv => //; conseq SampleDepDLet. by move: F; auto.
byphoare (: dt = d' /\ du = F ==> _) => //; proc. 
by rnd; skip; move => &1 /= [-> ->]; apply mu_eq; case.
qed.

(* TOTHINK: This proof relies on an explicit enumeration of [bool].
   It should be possible to generalize the result to arbitary types *)
lemma distinguisher_ll (A <: Distinguisher) &m x : 
  islossless A.guess => 
  is_lossless (mk (fun (z : bool) => Pr[A.guess(x) @ &m : res = z])).
proof.
move => A_ll; rewrite /F /is_lossless muE {1}/predT /=. 
have <- : Pr[A.guess(x) @ &m : res = true \/ res = false] = 1%r. 
  by byphoare => //; conseq (:_ ==> true) => // /#.  
rewrite (eq_sum _ (fun (z : bool) => Pr[A.guess(x) @ &m : res = z])) => [z /=|].
  by rewrite muK; 1: exact: (adv_isdistr A).
rewrite (sumE_fin _ [true; false]) // 1:/# !big_cons big_nil /predT/=.
by rewrite Pr[mu_disjoint] 1:/#. 
qed.

lemma adv_sdist (A <: Distinguisher) &m d1 d2 : 
  `| Pr[Sample(A).main(d1) @ &m : res] - Pr[Sample(A).main(d2) @ &m : res] | 
  <=  sdist d1 d2.
proof.
rewrite !(Sample_dlet A).
pose F x := mk (fun (z : bool) => Pr[A.guess(x) @ &m : res = z]).
exact (ler_trans _ _ _ (sdist_upper_bound _ _ _) (sdist_dlet _ _ F)).
qed.

(* Part 2 : The distinguiser is given oracle acces to the distribution *)

module type Oracle = {
  proc get() : a
}.

module type Oracle_i = {
  include Oracle
  proc init(d : a distr) : unit
}.

module type Adversary (O : Oracle) = { 
  proc main() : bool
}.

module Count (O : Oracle_i) = { 
  var n : int
  
  proc init (d' : a distr) = {
    n <- 0;
    O.init(d');
  }

 proc get() = { 
    var r;

    n <- n + 1;
    r <@ O.get();
    return r;
  }
}.

(* main distringuisher game *)
module Game(A : Adversary, O:Oracle_i) = {
  module CO = Count(O)

  proc main(d) = {
    var r;

    CO.init(d);
    r <@ A(CO).main();
    return r;
  }
}.

(* adversary of reduction to sampling game *)
module B1(A : Adversary) = {
  var x' : a

  module Ox = {
    proc init(x : a) = { x' <- x; }
    proc get() = {return x'; }
  }

  proc guess(x : a) = {
    var r;

    Ox.init(x);
    r <@ A(Ox).main();
    return r;
  }
}.


(* always sample *)
module Os : Oracle_i = {
  var d : a distr
  proc init (d' : a distr) = { d <- d'; }
  proc get () = { var r; r <$ d; return r; }
}.

section. (* Reduction from single oracle call to sampling game *)

declare module A <: Adversary {B1,Os,Count}.

declare axiom A_ll :
  forall (O <: Oracle{A}), islossless O.get => islossless A(O).main.

(* global variables for eager/lazy proof *)
local module Var = { 
  var x : a  
  var b : bool 
  var d : a distr
}.

(* sample once *)
local module O1 : Oracle_i = {
  proc init (d' : a distr) = { Var.x <$ d'; }
  proc get () = { return Var.x; }
}.

(* conditional sampling - eager *)
local module O1e : Oracle_i = {
  proc init (d' : a distr) = { 
    Var.x <- witness;
    Var.d <- d'; 
    Var.b <- true; 
    if (Var.b) Var.x <$ Var.d ; 
  }

  proc get () = { Var.b <- false; return Var.x; }
}.

(* conditional sampling - lazy *)
local module O1l = {
  var d : a distr

  proc init(d') = { 
    Var.x <- witness;
    Var.d <- d'; 
    Var.b <- true; 
  }
  proc get() = { 
    if (Var.b) Var.x <$ Var.d; 
    Var.b <- false ; 
    return Var.x;
  }
}.

(* "Game" with conditional resampling at the end *)
local module Gr(O : Oracle_i) = {
  module CO = Count(O)

  proc main(d) = { 
    var r;

    CO.init(d);
    r <@ A(CO).main();
    if (Var.b) Var.x <$ Var.d;
    return r;
  }
}.

(* TOTHINK: Can this be strenthened by dropping the requirement that
d1 and d2 are lossless? The current proof uses the eager tactics to
swap the statement [if (Var.b) Var.x <$ Var.d;] over the call to the
adversary, which only works if the distributions are lossless. *)

(* TOTHINK: The assumption [A_ll] is only used in the final "up to
bad" call, where it seems unavoidable. This should be revisited once
restrictions on the number of calls become part of the EasyCrypyt
logic. *)

lemma sdist_oracle1 &m (d1 d2 : a distr) : 
   is_lossless d1 => is_lossless d2 =>
  (forall (O <: Oracle_i{Count,A}), 
     hoare[ A(Count(O)).main : Count.n = 0 ==> Count.n <= 1]) =>
  `| Pr[Game(A,Os).main(d1) @ &m : res] - Pr[Game(A,Os).main(d2) @ &m : res] | 
  <= sdist d1 d2.
proof.
move => d1_ll d2_ll A_bound. 
suff H : forall d', is_lossless d' =>
  Pr[Game(A, Os).main(d') @ &m : res] = Pr [Sample(B1(A)).main(d') @ &m : res].
+ by rewrite !H ?d1_ll ?d2_ll; apply (adv_sdist (B1(A))). 
move => d' d'_ll.
suff <-: Pr[Game(A, O1).main(d') @ &m : res] = Pr[Game(A, Os).main(d') @ &m : res].
+ byequiv => //; proc; inline *; wp. 
  by call(: Var.x{1} = B1.x'{2}); [proc; inline *|]; auto. 
byequiv => //.
transitivity Game(A,O1e).main 
  (={arg,glob A} /\ d{1} = d' ==> ={res}) 
  (={arg,glob A} /\ d{1} = d' ==> ={res}); 1,2: smt().
  by proc; inline *; rcondt{2} 7; auto; call(: ={Var.x}); 1: sim; auto => />.
transitivity Gr(O1l).main 
  (={arg,glob A} /\ d{1} = d' ==> ={res}) 
  (={arg,glob A} /\ d{1} = d' ==> ={res}); 1,2: smt().
  proc; inline *.
  seq 6 6 : (={glob Var, glob A}); 1: by auto.
  eager (H : if (Var.b) Var.x <$ Var.d; ~  if (Var.b) Var.x <$ Var.d; 
    : ={glob Var} ==> ={glob Var} )
    : (={glob A,glob Var} ) => //; 1: by sim. 
  eager proc H (={glob Var}) => //; 2: by sim.
  proc*; inline *; rcondf{2} 6; [ by auto | by sp; if; auto].
proc; inline*. 
seq 7 5 : (={r} /\ Var.d{1} = d'); last by if{1}; auto => />.
conseq (_ : _ ==> Count.n{1} <= 1 /\ Count.n{2} <= 1 => 
                  ={Count.n,r} /\ Var.d{1} = d')
       (_ : _ ==> Count.n <= 1) (_ : _ ==> Count.n <= 1); 1: smt().
+ by call (A_bound O1l); auto.
+ by call (A_bound Os); auto.
call (: 2 <= Count.n, 
        ={Count.n} /\ Var.d{1} = Os.d{2} /\ 0 <= Count.n{1} /\ 
        (Var.b <=> Count.n = 0){1} /\ Os.d{2} = d', 
        Var.d{1} = Os.d{2} /\ Os.d{2} = d' /\ 2 <= Count.n{2}).
- move=> O; exact (A_ll O).
- by proc; inline *; sp; if{1}; [wp; rnd|]; auto => /> /#. 
- by move => ? _; proc; inline*; sp; if; auto.
- by move => ?; proc; inline*; auto => /> /#. 
- by auto => /> /#.
qed.

end section.

(* Reduction from n oracle calls to single oracle call *)
abstract theory N1.

(* We need operators, because we need to define modules that use them *)
op [lossless] d1 : a distr.
op [lossless] d2 : a distr.
op N : { int | 0 < N } as N_pos.

section. 

declare module A <: Adversary {B1,Os,Count}.

declare axiom A_ll :
  forall (O <: Oracle{A}), islossless O.get => islossless A(O).main.

declare axiom A_bound : (forall (O <: Oracle_i{A,Count}), 
  hoare[ A(Count(O)).main : Count.n = 0 ==> Count.n <= N]).

local clone Hybrid as Hyb with
  type input <- unit,
  type output <- a,
  type inleaks <- unit,
  type outleaks <- unit,
  type outputA <- bool,
  op q <- N,
  lemma q_pos <- N_pos
  proof*.

local module Ob : Hyb.Orclb = {

  proc leaks () = { return (); }
  
  proc orclL () = {
    var r;

    r <$ d1;
    return r;
  }

  proc orclR () = {
    var r;

    r <$ d2;
    return r;
  }
}.

(* : Hyb.AdvOrclb *)
local module B (Ob : Hyb.Orclb) (O : Hyb.Orcl) = {
  module O' : Oracle = {
    proc init(d : a distr) = {}
    proc get = O.orcl
  }
    
  proc main() : bool = {
    var r; 
    
    (* Adding counting here simplifies the proof of the bound
      for Hyb.AdvCount(B(Ob, Hyb.OrclCount(O))).main below *)
    Count.n <- 0; 
    r <@ A(Count(O')).main();
    return r;
  }
}.

local module B' (Ob : Hyb.Orclb) (O : Hyb.Orcl) = {
  module O' : Oracle = {
    proc get = O.orcl
  }

  proc main = A(O').main
}.

local module C (O : Oracle) = {
  module O' = { proc orcl = O.get }

  proc main = Hyb.HybGame(B', Ob, O').main
}.

local lemma Osd1_Hyb &m :
   Pr[Game(A, Os).main(d1) @ &m : res] = Pr[ Hyb.Ln(Ob, B).main() @ &m : res ].
proof.
byequiv => //; proc; inline *; auto. 
call (: Os.d{1} = d1); [by proc; inline*; auto| by auto].
qed.

local lemma Osd2_Hyb &m :
   Pr[Game(A, Os).main(d2) @ &m : res] = Pr[ Hyb.Rn(Ob, B).main() @ &m : res ].
proof.
byequiv => //; proc; inline *; auto. 
call (: Os.d{1} = d2); [by proc; inline*; auto| by auto].
qed.

lemma sdist_oracleN &m : 
  `| Pr[Game(A,Os).main(d1) @ &m : res] - Pr[Game(A,Os).main(d2) @ &m : res] | 
  <= N%r * sdist d1 d2.
proof.
rewrite -ler_pdivr_mull -?normrZ; 1,2: smt(N_pos). 
rewrite Osd1_Hyb Osd2_Hyb. 
have /= <- := Hyb.Hybrid_restr (<: Ob) (<: B) _ _ _ _ _ &m (fun _ _ _ r => r).
- move => O; proc; inline *; sp; wp. 
  inline *.
  conseq (: Hyb.Count.c = Count.n) (: Count.n = 0 ==> Count.n <= N) => //. 
    by call (A_bound (<: B(Ob, Hyb.OrclCount(O)).O')).
  call (: Hyb.Count.c = Count.n) => //.
  by proc; inline *; auto; call(: true); auto.
- by islossless.
- islossless; exact d1_ll.
- islossless; exact d2_ll.
- move => Ob LR *; islossless. 
  by apply (A_ll (<: Count(B(Ob, LR).O'))); islossless.
have -> : Pr[Hyb.HybGame(B, Ob, Hyb.L(Ob)).main() @ &m : res] = 
          Pr[Game(C, Os).main(d1) @ &m : res].
  byequiv => //; proc; inline*; auto. 
  call(: ={glob Hyb.HybOrcl} /\ Os.d{2} = d1); last by auto.
  proc; inline *; sp.
  if; [smt() | by auto |].
  if; [smt()| by auto | by auto].
have -> : Pr[Hyb.HybGame(B, Ob, Hyb.R(Ob)).main() @ &m : res] = 
          Pr[Game(C, Os).main(d2) @ &m : res].
  byequiv => //; proc; inline*; auto. 
  call(: ={glob Hyb.HybOrcl} /\ Os.d{2} = d2); last by auto.
  proc; inline *; sp.
  if; [smt() | by auto |].
  if; [smt()| by auto | by auto].
apply (sdist_oracle1 C);[|exact d1_ll|exact d2_ll|].
- move => O O_ll; islossless; 2: by rewrite DInterval.weight_dinter; smt(N_pos).
  by apply (A_ll (<: B'(Ob, Hyb.HybOrcl(Ob, C(O).O')).O')); islossless. 
move => O; proc.
call(: if Hyb.HybOrcl.l <= Hyb.HybOrcl.l0 then Count.n = 0 else Count.n = 1).
- proc; inline *; if; 1: (by auto; smt()); if; 2: by auto; smt(). 
  by auto; call(: true) => //; auto; smt().
auto; smt(DInterval.supp_dinter).
qed.

end section.

end N1.

abstract theory ROM.

import SmtMap.

type in_t.
op [lossless] d1 : a distr.
op [lossless] d2 : a distr.
op N : { int | 0 < N } as N_pos.

clone PROM.FullRO as R1 with 
  type in_t <- in_t, 
  type out_t <- a, 
  type d_in_t <- unit,
  type d_out_t <- bool,
  op dout <- fun _ => d1
  proof*.

clone PROM.FullRO as R2 with 
  type in_t <- in_t, 
  type out_t <- a, 
  type d_in_t <- unit,
  type d_out_t <- bool,
  op dout <- fun _ => d2
  proof*.

module O1 = R1.RO.
module O2 = R2.RO.

(* This allows us to PROM rather then ROM, and the former has better
infrastructure (e.g., for splitting into muliple oracles *) 

module type Distinguisher (O : R1.RO) = {
  proc distinguish(_ : unit) : bool {O.get O.set O.sample}
}.

(* TOTHINK: Calls to [sample] and [get] do not actually provide any
information about the underying distribution. However, unless one uses
a lazy oracle, [sample] does require an oracle call. *)
module Wrap (O : R1.RO) : R1.RO = {
  var dom : in_t fset

  proc init() = { 
    dom <- fset0 ; 
    O.init(); 
  }

  proc get(x) = { 
    var r;
    dom <- dom `|` fset1 x; 
    r <@ O.get(x); 
    return r;
  }
  
  proc set(x,v) = {
    dom <- dom `|` fset1 x; 
    O.set(x,v); 
  }

  proc sample(x) = { 
    get(x);
  }

  (* never called by our distinguisher *)
  proc rem = O.rem
}.

section.

declare module D <: Distinguisher {Os, O1,O2, Count, B1, Wrap}.

declare axiom D_ll : forall (O <: R1.RO{D}), 
  islossless O.get => islossless D(O).distinguish.

local module Cache (O : Oracle) : R1.RO = {
  var m : (in_t,a) fmap 

  proc init () = { m <- empty; }

  proc get(i) = {
    var x; 

    if (! i \in m) {
      x <@ O.get();
      m.[i] <- x;
    }
    return oget (m.[i]);
  }

  proc set(x : in_t, y : a) = {
    m.[x] <- y;
  }

  proc sample(x: in_t) = {
    get(x);
  }
  
  (* never called by our distinguisher *)
  proc rem(x: in_t) = {}
}.

local module A (O : Oracle) = {
  module O' = Wrap(Cache(O))
 
  proc main () = {
     var r;

     O'.init();
     r <@ D(O').distinguish();
     return r;
  }
}.

local clone N1 as N1 with
  op d1 <- d1,
  op d2 <- d2,
  axiom d1_ll <- d1_ll,
  axiom d2_ll <- d2_ll,
  op N <- N,
  axiom N_pos <- N_pos
  proof*.

lemma sdist_ROM  &m : 
 (forall (O <: R1.RO{Wrap,D}), 
   hoare [ D(Wrap(O)).distinguish : Wrap.dom = fset0 ==> card Wrap.dom <= N]) =>
  `| Pr [R1.MainD(D,O1).distinguish() @ &m : res] - 
     Pr [R1.MainD(D,O2).distinguish() @ &m : res] |
  <= N%r * sdist d1 d2.
proof.
move => D_bound. 
have -> : Pr[R1.MainD(D,O1).distinguish() @ &m : res] = 
          Pr[Game(A,Os).main(d1) @ &m : res].
- byequiv => //; proc; inline *; wp.
  call(: ={m}(O1,Cache) /\ Os.d{2} = d1); last by auto.
  + proc; inline *; sp.
    if{2}; [by rcondt{1} 2; auto| rcondf{1} 2; auto; smt(d1_ll)].
  + by proc; inline *; auto.
  + proc; inline *; sp.
    if{2}; [by rcondt{1} 2; auto| rcondf{1} 2; auto; smt(d1_ll)].
have -> : Pr[R1.MainD(D,O2).distinguish() @ &m : res] = 
          Pr[Game(A,Os).main(d2) @ &m : res].
- byequiv => //; proc; inline *; wp.
  call(: ={m}(O2,Cache) /\ Os.d{2} = d2); last by auto.
  + proc; inline *; sp.
    if{2}; [by rcondt{1} 2; auto| rcondf{1} 2; auto; smt(d2_ll)].
  + by proc; inline *; auto.
  + proc; inline *; sp.
    if{2}; [by rcondt{1} 2; auto| rcondf{1} 2; auto; smt(d1_ll)].
apply (N1.sdist_oracleN A _ _ &m) => [O get_ll|].
- by islossless; apply (D_ll (<: Wrap(Cache(O)))); islossless. 
move => O; proc; inline *; sp.
conseq (: Count.n <= card Wrap.dom /\ fdom Cache.m = Wrap.dom) 
       (: Wrap.dom = fset0 ==> card Wrap.dom <= N); 1,2: smt(). 
- by call (D_bound (<: Cache(Count(O)))).
have Wget : hoare [ Wrap(Cache(Count(O))).get : 
  Count.n <= card Wrap.dom /\ fdom Cache.m = Wrap.dom ==> 
  Count.n <= card Wrap.dom /\ fdom Cache.m = Wrap.dom].
- proc; inline*; wp; sp; if. 
  + auto; call(: true); auto => /> &1 cnt_n x_cache a.
    split; last by rewrite fdom_set.
    by rewrite !fcardU fsetI1 !mem_fdom x_cache /= fcards0 fcard1 /#.
  + auto => /> &1 cnt_n x_cache.
    split; last by apply/fsetP => x; rewrite !inE !mem_fdom /#.
    rewrite fcardU fcard1 fsetI1 mem_fdom x_cache /=.
    smt (fcardU fcard1 fcard_ge0).
call (: Count.n <= card Wrap.dom /\ fdom Cache.m = Wrap.dom); last first.
  by auto; smt(fcards0 fdom0).
- proc; inline*; auto => /> &1. 
  rewrite !fcardU !fcard1 fsetI1 mem_fdom fdom_set => H.
  smt (fcardU fcard1 fcards0 fcard_ge0).
- by proc; inline Wrap(Cache(Count(O))).sample; call Wget.
qed.

end section.

end ROM.

end Dist.
