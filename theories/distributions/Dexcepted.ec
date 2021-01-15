(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore Distr FSet Dfilter StdRing.
(*---*) import RField StdOrder.RealOrder.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op (\) (d : 'a distr) (P : 'a -> bool) : 'a distr = dscale (dfilter d P).

lemma supp_dexcepted (x:'a) d P :
  support (d \ P) x <=> (support d x /\ !P x).
proof. by rewrite supp_dscale supp_dfilter /predI /predC. qed.

lemma dexcepted1E d P (x : 'a) :
  mu1 (d \ P) x
  = if   P x
    then 0%r
    else (mu1 d x / (weight d - mu d (P))).
proof. by rewrite dscale1E weight_dfilter dfilter1E; case: (P x). qed.

lemma nosmt dexcepted1E_notin (d : 'a distr) P x:
  !P x => mu1 (d \ P) x = (mu1 d x / (weight d - mu d (P))).
proof. by rewrite dexcepted1E => ->. qed.

lemma nosmt dexcepted1E_in d P (x:'a):
  P x => mu1 (d \ P) x = 0%r.
proof. by rewrite dexcepted1E => ->. qed.

lemma dexceptedE d P (E : 'a -> bool) :
  mu (d \ P) E
  = mu d (predI E (predC (P))) / (weight d - mu d (P)).
proof. by rewrite dscaleE weight_dfilter dfilterE. qed.

lemma nosmt weight_dexcepted (d:'a distr) P :
  weight (d \ P) = b2r (weight d <> mu d (P)).
proof.
rewrite weight_dscale weight_dfilter /b2r subr_eq0.
by case: (weight d = mu d (P)).
qed.

lemma dexcepted_ll (d : 'a distr) P:
  is_lossless d => mu d P < 1%r =>
  is_lossless (d \ P).
proof.
move=> d_ll P_neq_d.
by rewrite /is_lossless  weight_dexcepted d_ll /#.
qed.

lemma dexcepted_uni (d : 'a distr) P:
  is_uniform d => is_uniform (d \ P).
proof.
move=> uni x y; rewrite !supp_dexcepted !dexcepted1E.
by move=> [? ->] [? ->] /=; congr; apply uni.
qed.

(* -------------------------------------------------------------------- *)
lemma dexcepted_dscale (dt : 'a distr) X: dt \ X = (dscale dt) \ X.
proof.
case: (weight dt = 0%r)=> [dt_is_null|dt_not_null].
+ apply/eq_distr=> x; rewrite !dexcepted1E !dscaleE dt_is_null /=.
  rewrite (@ler_anti (mu1 dt x) 0%r _) //.
  by rewrite ge0_mu /= -{1}dt_is_null mu_sub /#.
apply/eq_distr=> x; rewrite !dexcepted1E; case: (X x)=> // x_notin_X.
rewrite dscale1E -mulrA -invfM !dscaleE; congr; congr.
by rewrite mulrDr -mulNr (@mulrCA _ (-mu dt X)) divrr.
qed.

(* -------------------------------------------------------------------- *)
abstract theory TwoStepSampling.
type i, t.

op dt: i -> t distr.

module S = {
  proc direct(x : i, X : i -> t -> bool) = {
    var r;

    r <$ dt x \ X x;
    return r;
  }

  proc indirect(x : i, X : i -> t -> bool) = {
    var r;

    r <$ dt x;
    if (X x r) {
      r <$ dt x \ X x;
    }
    return r;
  }
}.

(* -------------------------------------------------------------------- *)
lemma pr_direct &m x' X' P:
  Pr[S.direct(x',X') @ &m: P res] = mu (dt x' \ X' x') P.
proof.
byphoare (: x = x' /\ X = X' ==> _)=> //=.
by proc; rnd P; auto.
qed.

phoare phoare_direct x' X' P:
  [ S.direct: x = x' /\ X = X' ==> P res ] = (mu (dt x' \ X' x') P).
proof. by bypr=> &m [] -> ->; exact/(@pr_direct &m x' X' P). qed.

(* -------------------------------------------------------------------- *)
lemma pr_indirect &m x' X' P:
  Pr[S.indirect(x',X') @ &m: P res] = weight (dt x') * mu (dt x' \ X' x') P.
proof.
byphoare (: x = x' /\ X = X' ==> _)=> //=.
case: (forall x, (x \in dt x' => !P x) \/ !(P x /\ !X' x' x)).
+ move=> P_nsub_supp; hoare.
  + move=> &m' [#] <<*>; rewrite eq_sym dexceptedE mulf_eq0; right.
    rewrite mulf_eq0; left; apply/mu0_false.
    move=> x @/predI @/predC x_in_dt.
    by case: (P_nsub_supp x)=> [/(_ x_in_dt) ->|].
  proc. seq 1: (r \in dt x /\ x = x' /\ X = X'); auto.
  if; auto=> /> &m'.
  + move=> _ _ r /supp_dexcepted [] r_in_dt.
    by case: (P_nsub_supp r)=> [/(_ r_in_dt) ->|/negb_and /implybE /contra].
  move=> r_in_dt ; case: (P_nsub_supp r{m'})=> [/(_ r_in_dt) -> //|].
  by rewrite negb_and -implybE=> /contra.
rewrite negb_forall=> - [a]; rewrite /= negb_or=> /> + Pa; rewrite Pa /=.
move=> a_in_dt a_notin_X.
proc. alias 2 r0 = r.
phoare split (mu (dt x) (predI P (predC (X' x'))))
             (mu (dt x) (X x) * mu (dt x \ X x) P)
             : (P r0 /\ !X' x' r0).
+ move=> /= &m' [] ->> ->> {&m'}; rewrite dexceptedE.
  rewrite -{1}(mulr1 (mu (dt x') (predI _ _))).
  rewrite -(@divrr (weight (dt x') - mu (dt x') (X' x'))).
  + rewrite -mu_not; apply/ltr0_neq0.
    by rewrite witness_support; exists a; rewrite /predC a_in_dt a_notin_X.
  rewrite mulrA mulrA mulrA -mulrDl; congr.
  by rewrite mulrDr mulrC mulrN (mulrC (_ _ (X' x'))) subrK.
+ seq  2: (P r0 /\ !X' x' r0)
          (mu (dt x') (predI P (predC (X' x')))) 1%r
                                               _ 0%r
          (r0 = r /\ x = x' /\ X = X')=> //=.
  + by auto.
  + by wp; rnd (predI P (predC (X' x'))); auto=> />.
  + by rcondf 1.
  by hoare; conseq (: _ ==> true)=> // /#.
seq 2: (!X' x' r0)
                     _ 0%r
       (mu (dt x') (X' x')) (mu (dt x' \ X' x') P)
       (r0 = r /\ x = x' /\ X = X')=> //=.
+ by auto.
+ by hoare; rcondf 1=> //; auto=> /#.
+ by wp; rnd.
by rcondt 1=> //; rnd P; skip=> /#.
qed.

phoare phoare_indirect x' X' P:
  [ S.indirect: x = x' /\ X = X' ==> P res ]
  = (weight (dt x) * mu (dt x \ X x) P).
proof. by bypr=> &m [] -> ->; rewrite (@pr_indirect &m x' X' P). qed.

(* -------------------------------------------------------------------- *)
lemma ll_pr_indirect &m x' X' P:
     is_lossless (dt x')
  => Pr[S.indirect(x',X') @ &m: P res] = mu (dt x' \ X' x') P.
proof. by move=> dt_ll; rewrite (@pr_indirect &m x' X' P) dt_ll. qed.

phoare ll_phoare_indirect x' X' P:
  [ S.indirect: x = x' /\ X = X' /\ is_lossless (dt x') ==> P res ]
  = (mu (dt x \ X x) P).
proof.
by bypr=> &m [] -> [] -> dt_ll; rewrite (@ll_pr_indirect &m x' X' P).
qed.

(* -------------------------------------------------------------------- *)
lemma indirect_direct &m x X P:
    Pr[S.indirect(x,X) @ &m: P res]
  = weight (dt x) * Pr[S.direct(x,X) @ &m: P res].
proof. by rewrite (@pr_direct &m x X P) (@pr_indirect &m x X P). qed.

lemma ll_direct_indirect &m x X P:
     is_lossless (dt x)
  => Pr[S.direct(x,X) @ &m: P res] = Pr[S.indirect(x,X) @ &m: P res].
proof. by rewrite (@indirect_direct &m x X P)=> ->. qed.

(* -------------------------------------------------------------------- *)
equiv ll_direct_indirect_eq: S.direct ~ S.indirect:
  ={x, X} /\ is_lossless (dt x{1}) ==> ={res}.
proof.
bypr (res{1}) (res{2})=> //= &1 &2 a [#] <<*> <- <- dt_ll.
rewrite (@indirect_direct &2 x{1} X{1} (pred1 a)) dt_ll /=.
by byequiv (: ={arg} ==> ={res})=> //=; sim.
qed.

end TwoStepSampling.

(* -------------------------------------------------------------------- *)
abstract theory WhileSampling.
type input, t.

op dt: input -> t distr.

module SampleE = {
  proc init () = { }

  proc sample(i : input, test) = {
    var r;

    r <$ dt i \ test i;
    return r;
  }
}.

module SampleI = {
  proc init () = { }

  proc sample(i:input, test) = {
    var r;
    r <$ dt i;
    if (test i r) {
      r <$ dt i \ test i;
    }
    return r;
  }
}.

module SampleWi = {
  proc init () = { }

  proc sample(i : input, r : t, test) = {
    while (test i r) {
      r <$ dt i;
    }
    return r;
  }
}.

module SampleW = {
  proc init () = { }

  proc sample(i : input, test) = {
    var r;
    r <$ dt i;
    r <@ SampleWi.sample(i, r, test);
    return r;
  }
}.

(* -------------------------------------------------------------------- *)
lemma pr_sampleE &m x X P :
  Pr[SampleE.sample(x, X) @ &m : P res] = mu (dt x \ X x) P.
proof.
by byphoare (_ : i = x /\ test = X ==> P res) => //; proc; rnd P; skip.
qed.

lemma phoare_sampleE P :
  phoare [SampleE.sample : true ==> P res ] = (mu (dt i \ test i) P).
proof. by bypr=> &m _; apply (@pr_sampleE &m i{m} test{m} P). qed.

(* -------------------------------------------------------------------- *)
section.
local clone TwoStepSampling as TS with
  type i  <- input,
  type t  <- t,
    op dt <- dt.

lemma pr_sampleI &m x' X' P :
  is_lossless (dt x') =>
  Pr[SampleI.sample(x',X') @ &m : P res] = mu (dt x' \ X' x') P.
proof.
move=> d_ll; rewrite -(@TS.ll_pr_indirect &m x' X' P) //.
byequiv (: ={arg} ==> ={res})=> //=.
proc; seq  1  1: (={r} /\ i{1} = x{2} /\ test{1} = X{2}).
+ by auto.
by if=> //=; auto.
qed.
end section.

phoare phoare_sampleI P :
  [ SampleI.sample : is_lossless (dt i) ==> P res ] = (mu (dt i \ test i) P).
proof. by bypr=> &m; apply (@pr_sampleI &m i{m} test{m} P). qed.

(* -------------------------------------------------------------------- *)
lemma pr_sampleWi &m x y X P :
  is_lossless (dt x) =>
    Pr[SampleWi.sample(x,y,X) @ &m : P res]
  = if X x y then mu (dt x \ X x) P else b2r (P y).
proof.
move=> dt_ll.
case: (X x y)=> [y_in_Xx|y_notin_Xx]; last first.
+ case: (P y)=> [y_in_P|y_notin_P].
  + byphoare (: i = x /\ r = y /\ test = X ==> P res)=> //.
    by proc; rcondf 1; auto.
  byphoare (: i = x /\ r = y /\ test = X ==> P res)=> //.
  by hoare; proc; rcondf 1; auto.
byphoare (: i = x /\ r = y /\ test = X ==> P res)=> //; proc=> /=.
case @[ambient]: (mu (dt x) (X x) = weight (dt x))=> Hpt.
+ hoare.
  + by move=> />; rewrite dexceptedE Hpt.
  while (X x r /\ i = x /\ test = X)=> //=.
  auto=> &m' [#] _ -> -> _ r; move: (mu_in_weight (X x) (dt x) r).
  by rewrite Hpt.
while (i = x /\ test = X) (if test x r then 1 else 0) 1 (mu (dt x) (predC (X x)))=> //=.
+ smt().
+ move=> ih. alias 2 r0 = r.
  (** TRANSITIVITY FOR PHOARE!! **)
  phoare split (mu (dt x) (predI P (predC (X x))))
               (mu (dt x) (X x) * mu (dt x \ X x) P)
               : (P r0 /\ !X x r0).
  + move=> &m' [#] -> -> _ /=; rewrite dexceptedE.
    rewrite -{1}(mulr1 (mu (dt x) (predI _ _))).
    rewrite -(@divrr (weight (dt x) - mu (dt x) (X x))).
    + smt().
    rewrite mulrA mulrA -mulrDl; congr.
    by rewrite mulrDr mulrC mulrN (mulrC (_ _ (X x))) subrK dt_ll. (* dt_ll *)
  + seq  2: (P r0 /\ !X x r0)
            (mu (dt x) (predI P (predC (X x)))) 1%r
                                              _ 0%r
            (r0 = r /\ i = x /\ test = X)=> //=.
    + by auto.
    + by wp; rnd (predI P (predC (X x))); auto=> />.
    + by rcondf 1.
    by hoare; conseq (: _ ==> true)=> // /#.
  seq 2: (!X x r0)
                         _ 0%r
         (mu (dt x) (X x)) (mu (dt x \ X x) P)
         (r0 = r /\ i = x /\ test = X)=> //=.
  + by auto.
  + by hoare; rcondf 1=> //; auto=> /#.
  + by wp; rnd.
  by conseq ih=> &m' />; rewrite dexceptedE.
+ by auto.
split.
+ by move=> &m' />; rewrite mu_not [smt(mu_bounded)].
by move=> z; conseq (: _ ==> !X x r)=> />; rnd; skip.
qed.

lemma phoare_sampleWi P :
    phoare [SampleWi.sample : is_lossless (dt i) ==> P res]
  = (if test i r then mu (dt i \ test i) P else b2r (P r)).
proof. by bypr=> &m'; exact/(@pr_sampleWi &m' i{m'} r{m'} test{m'} P). qed.

(* -------------------------------------------------------------------- *)
lemma pr_sampleW &m x X P :
  is_lossless (dt x) =>
  Pr[SampleW.sample(x, X) @ &m : P res] = mu (dt x \ X x) P.
proof.
move=> dt_ll.
byphoare (: i = x /\ test = X ==> P res)=> //; proc=> /=.
case @[ambient]: (mu (dt x) (X x) = weight (dt x))=> Hpt.
+ conseq (: : = 0%r)=> //.
  + by move=> &m' _; rewrite dexceptedE Hpt.
  seq 1 : true _ 0%r 0%r _ (i = x /\ test = X /\ X x r)=> //.
  + auto=> &m' [#] -> -> r; move: (mu_in_weight (X x) (dt x) r).
    by rewrite Hpt.
  call (: is_lossless (dt x) /\ i = x /\ test = X /\ X x r ==> P res)=> //.
  by conseq (phoare_sampleWi P)=> // &m' [#] _ -> -> ->; rewrite dexceptedE Hpt.
alias 2 r0 = r.
(** TRANSITIVITY FOR PHOARE!! **)
phoare split (mu (dt x) (predI P (predC (X x))))
             (mu (dt x) (X x) * mu (dt x \ X x) P)
             : (P r0 /\ !X x r0).
+ move=> &m' _ /=; rewrite dexceptedE.
  rewrite -{1}(mulr1 (mu (dt x) (predI _ _))).
  rewrite -(@divrr (weight (dt x) - mu (dt x) (X x))).
  + smt().
  rewrite mulrA mulrA -mulrDl; congr.
  by rewrite mulrDr mulrC mulrN (mulrC (_ _ (X x))) subrK dt_ll. (* dt_ll *)
+ seq  2: (P r0 /\ !X x r0)
          (mu (dt x) (predI P (predC (X x)))) 1%r
                                            _ 0%r
          (r0 = r /\ i = x /\ test = X)=> //=.
  + by auto.
  + by wp; rnd (predI P (predC (X x))); auto=> />.
  + by inline *; rcondf 4; auto.
  by hoare; conseq (: true)=> />.
seq 2: (!X x r0)
                       _ 0%r
       (mu (dt x) (X x)) (mu (dt x \ X x) P)
       (r0 = r /\ i = x /\ test = X)=> //=.
+ by auto.
+ by hoare; inline *; rcondf 4; auto=> &m' /#.
+ by wp; rnd.
call (: is_lossless (dt x) /\ i = x /\ test = X /\ X x r ==> P res)=> //.
+ by conseq (phoare_sampleWi P)=> // &m' />.
by skip=> &m' />.
qed.

phoare phoare_sampleW P :
  [ SampleW.sample: is_lossless (dt i) ==> P res ] = (mu (dt i \ test i) P).
proof. by bypr=> &m; exact/(@pr_sampleW &m i{m} test{m} P). qed.

(* -------------------------------------------------------------------- *)
equiv sampleE_sampleI : SampleE.sample ~ SampleI.sample :
  ={i, test} /\ is_lossless (dt i{1}) ==> ={res}.
proof.
bypr (res{1}) (res{2})=> /> &m1 &m2 a <- <- d_ll.
rewrite (@pr_sampleE &m1 i{m1} test{m1} (pred1 a)).
by rewrite (@pr_sampleI &m2 i{m1} test{m1} (pred1 a)).
qed.

lemma sampleE_sampleI_pr &m x X P :
     is_lossless (dt x)
  => Pr[SampleE.sample(x,X) @ &m: P res] = Pr[SampleI.sample(x,X) @ &m: P res].
proof. by move=> dt_ll; byequiv sampleE_sampleI. qed.

equiv sampleE_sampleWi: SampleE.sample ~ SampleWi.sample :
  ={i,test} /\ is_lossless (dt i{1}) /\ test{2} i{2} r{2} ==> ={res}.
proof.
bypr (res{1}) (res{2})=> /> &m1 &m2 a <- <- d_ll Htr.
rewrite (@pr_sampleE &m1 i{m1} test{m1} (pred1 a)).
by rewrite (@pr_sampleWi &m2 i{m1} r{m2} test{m1} (pred1 a)) // Htr.
qed.

lemma sampleE_sampleWi_pr &m x y X P:
     is_lossless (dt x)
  => X x y
  => Pr[SampleE.sample(x,X) @ &m: P res] = Pr[SampleWi.sample(x,y,X) @ &m: P res].
proof. by move=> dt_ll y_in_Xx; byequiv sampleE_sampleWi. qed.

equiv sampleE_sampleW : SampleE.sample ~ SampleW.sample :
  ={i,test} /\ is_lossless (dt i{1}) ==> ={res}.
proof.
bypr (res{1}) (res{2})=> /> &m1 &m2 a <- <- d_ll.
rewrite (@pr_sampleE &m1 i{m1} test{m1} (pred1 a)).
by rewrite (@pr_sampleW &m2 i{m1} test{m1} (pred1 a)).
qed.

lemma sampleE_sampleW_pr &m x X P:
     is_lossless (dt x)
  => Pr[SampleE.sample(x,X) @ &m: P res] = Pr[SampleW.sample(x,X) @ &m: P res].
proof. by move=> dt_ll; byequiv sampleE_sampleW. qed.
end WhileSampling.

(* -------------------------------------------------------------------- *)
abstract theory WhileSamplingFixedTest.
type input, t.

op dt: input -> t distr.
op test: input -> t -> bool.

module SampleE = {
  proc init () = { }

  proc sample(i : input) = {
    var r;

    r <$ dt i \ test i;
    return r;
  }
}.

module SampleI = {
  proc init () = { }

  proc sample(i:input) = {
    var r;
    r <$ dt i;
    if (test i r) {
      r <$ dt i \ test i;
    }
    return r;
  }
}.

module SampleWi = {
  proc init () = { }

  proc sample(i : input, r : t) = {
    while (test i r) {
      r <$ dt i;
    }
    return r;
  }
}.

module SampleW = {
  proc init () = { }

  proc sample(i : input) = {
    var r;
    r <$ dt i;
    r <@ SampleWi.sample(i, r);
    return r;
  }
}.

(* -------------------------------------------------------------------- *)
section.
local clone WhileSampling as WS with
  type input <- input,
  type     t <- t,
    op    dt <- dt.

(* -------------------------------------------------------------------- *)
local lemma sampleE_fixed &m x P :
    Pr[SampleE.sample(x) @ &m : P res]
  = Pr[WS.SampleE.sample(x,test) @ &m : P res].
proof.
byequiv (: ={i} /\ test{2} = test ==> ={res})=> //=.
by proc; auto.
qed.

lemma pr_sampleE &m x P :
  Pr[SampleE.sample(x) @ &m : P res] = mu (dt x \ test x) P.
proof. by rewrite (@sampleE_fixed &m x P) (@WS.pr_sampleE &m x test P). qed.

phoare phoare_sampleE P :
  [ SampleE.sample : true ==> P res ] = (mu (dt i \ test i) P).
proof. by bypr=> &m _; exact/(@pr_sampleE &m i{m} P). qed.

(* -------------------------------------------------------------------- *)
local lemma sampleI_fixed &m x P :
    Pr[SampleI.sample(x) @ &m : P res]
  = Pr[WS.SampleI.sample(x,test) @ &m : P res].
proof.
byequiv (: ={i} /\ test{2} = test ==> ={res})=> //=.
proc=> /=. seq 1 1: (={i, r} /\ test{2} = test).
+ by auto.
by if; auto.
qed.

lemma pr_sampleI &m x P :
  is_lossless (dt x)
  => Pr[SampleI.sample(x) @ &m : P res] = mu (dt x \ test x) P.
proof.
move=> dt_ll.
by rewrite (@sampleI_fixed &m x P) (@WS.pr_sampleI &m x test P dt_ll).
qed.

phoare phoare_sampleI P :
  [ SampleI.sample: is_lossless (dt i) ==> P res ] = (mu (dt i \ test i) P).
proof. bypr=> &m; exact/(@pr_sampleI &m i{m} P). qed.

(* -------------------------------------------------------------------- *)
local lemma sampleWi_fixed &m x y P :
    Pr[SampleWi.sample(x,y) @ &m : P res]
  = Pr[WS.SampleWi.sample(x,y,test) @ &m : P res].
proof.
byequiv (: ={i,r} /\ test{2} = test ==> ={res})=> //=.
by proc=> /=; while (={i,r} /\ test{2} = test)=> //=; auto.
qed.

lemma pr_sampleWi &m x y P :
  is_lossless (dt x)
  =>   Pr[SampleWi.sample(x,y) @ &m : P res]
     = if test x y then mu (dt x \ test x) P else b2r (P y).
proof.
move=> dt_ll.
rewrite (@sampleWi_fixed &m x y P).
by rewrite (@WS.pr_sampleWi &m x y test P).
qed.

phoare phoare_sampleWi P :
  [ SampleWi.sample : is_lossless (dt i) ==> P res ]
  = (if test i r then mu (dt i \ test i) P else b2r (P r)).
proof. by bypr=> &m; exact/(@pr_sampleWi &m i{m} r{m} P). qed.

(* -------------------------------------------------------------------- *)
local lemma sampleW_fixed &m x P :
    Pr[SampleW.sample(x) @ &m : P res]
  = Pr[WS.SampleW.sample(x,test) @ &m : P res].
proof.
byequiv (: ={i} /\ test{2} = test ==> ={res})=> //=.
proc; inline *; wp.
by while (={i0,r0} /\ test0{2} = test)=> //=; auto.
qed.

lemma pr_sampleW &m x P :
  is_lossless (dt x)
  => Pr[SampleW.sample(x) @ &m : P res] = mu (dt x \ test x) P.
proof.
move=> dt_ll.
rewrite (@sampleW_fixed &m x P).
by rewrite (@WS.pr_sampleW &m x test P).
qed.

phoare phoare_sampleW P :
  [ SampleW.sample: is_lossless (dt i) ==> P res ] = (mu (dt i \ test i) P).
proof. by bypr=> &m; exact/(@pr_sampleW &m i{m} P). qed.

(* -------------------------------------------------------------------- *)
equiv sampleE_sampleI : SampleE.sample ~ SampleI.sample :
  ={i} /\ is_lossless (dt i{1}) ==> ={res}.
proof.
bypr (res{1}) (res{2})=> /> &m1 &m2 a <- dt_ll.
by rewrite (@pr_sampleE &m1 i{m1} (pred1 a)) (@pr_sampleI &m2 i{m1} (pred1 a)).
qed.

lemma sampleE_sampleI_pr &m x P:
  is_lossless (dt x)
  => Pr[SampleE.sample(x) @ &m: P res] = Pr[SampleI.sample(x) @ &m: P res].
proof. by move=> dt_ll; byequiv sampleE_sampleI. qed.

equiv sampleE_sampleWi : SampleE.sample ~ SampleWi.sample :
  ={i} /\ is_lossless (dt i{1}) /\ test i{2} r{2} ==> ={res}.
proof.
bypr (res{1}) (res{2})=> /> &m1 &m2 a <- dt_ll Htr.
rewrite (@pr_sampleE &m1 i{m1} (pred1 a)).
by rewrite (@pr_sampleWi &m2 i{m1} r{m2} (pred1 a)) // Htr.
qed.

lemma sampleE_sampleWi_pr &m x y P:
     is_lossless (dt x)
  => test x y
  => Pr[SampleE.sample(x) @ &m: P res] = Pr[SampleWi.sample(x,y) @ &m: P res].
proof. by move=> dt_ll test_i_r; byequiv sampleE_sampleWi. qed.

equiv sampleE_sampleW : SampleE.sample ~ SampleW.sample :
  ={i} /\ is_lossless (dt i{1}) ==> ={res}.
proof.
bypr (res{1}) (res{2})=> /> &m1 &m2 a <- dt_ll.
by rewrite (@pr_sampleE &m1 i{m1} (pred1 a)) (@pr_sampleW &m2 i{m1} (pred1 a)).
qed.

lemma sampleE_sampleW_pr &m x P:
     is_lossless (dt x)
  => Pr[SampleE.sample(x) @ &m: P res] = Pr[SampleW.sample(x) @ &m: P res].
proof. by move=> dt_ll; byequiv sampleE_sampleW. qed.
end section.

end WhileSamplingFixedTest.
