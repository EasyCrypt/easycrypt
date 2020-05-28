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

(* ==================================================================== *)
abstract theory ProdSampling.
type t1, t2.

module S = {
  proc sample(d1 : t1 distr, d2 : t2 distr) : t1 * t2 = {
    var r;

    r <$ d1 `*` d2;
    return r;
  }

  proc sample2(d1 : t1 distr, d2 : t2 distr) : t1 * t2 = {
    var r1, r2;

    r1 <$ d1;
    r2 <$ d2;
    return (r1,r2);
  }
}.

(* -------------------------------------------------------------------- *)
equiv sample_sample2 : S.sample ~ S.sample2 : ={d1, d2} ==> ={res}.
proof.
bypr (res{1}) (res{2}) => // &m1 &m2 a [<- <-].
have ->: Pr[S.sample(d1{m1}, d2{m1}) @ &m1 : res = a] = mu1 (d1{m1} `*` d2{m1}) a.
+ by byphoare (_ : d1{m1} = d1 /\ d2{m1} = d2 ==> _) => //=; proc; rnd; skip.
case: a => a1 a2; rewrite dprod1E.
byphoare (_ : d1{m1} = d1 /\ d2{m1} = d2 ==> _) => //=.
proc; seq  1: (r1 = a1) (mu1 d1 a1) (mu1 d2 a2) _ 0%r true=> //=.
+ by rnd. + by rnd. + by hoare; auto=> /> ? ->.
qed.
end ProdSampling.

(* ==================================================================== *)
abstract theory DLetSampling.
type t, u.

module SampleDep = {
  proc sample2(dt : t distr, du : t -> u distr) : t * u = {
    var t, u;

    t <$ dt;
    u <$ du t;
    return (t, u);
  }

  proc sample(dt : t distr, du : t -> u distr) : u = {
    var t, u;

    t <$ dt;
    u <$ du t;
    return u;
  }
}.

module SampleDLet = {
  proc sample2(dt : t distr, du : t -> u distr) : t * u = {
    var tu;

    tu <$ dlet dt (fun t => dunit t `*` du t);
    return tu;
  }

  proc sample(dt : t distr, du : t -> u distr) : u = {
    var u;

    u <$ dlet dt du;
    return u;
  }
}.

(* -------------------------------------------------------------------- *)
equiv SampleDepDLet2 :
  SampleDep.sample2 ~ SampleDLet.sample2 : ={dt, du} ==> ={res}.
proof.
pose F dt du := mu1 (dlet<:t, t * u> dt (fun t => dunit t `*` du t)).
bypr (res{1}) (res{2}) => // &m1 &m2 x [<- <-].
have ->: Pr[SampleDLet.sample2(dt{m1}, du{m1}) @ &m2 : res = x] = F dt{m1} du{m1} x.
+ by byphoare (_ : dt{m1} = dt /\ du{m1} = du ==> _) => //=; proc; rnd; skip. 
case: x => x1 x2; have -> :
  F dt{m1} du{m1} (x1, x2) = mu1 dt{m1} x1 * mu1 (du{m1} x1) x2.
+ rewrite /F dlet1E /= 1?(@sumD1 _ x1) /=.
  * apply: (@summable_le (mu1 dt{m1})) => /=; first by apply: summable_mu1.
    by move=> x; rewrite normrM ler_pimulr ?normr_ge0 ?ger0_norm.
  rewrite dprod1E dunit1E /= sum0_eq //= => x; case: (x = x1) => //=.
  by move=> ne_x_x1; rewrite dprod1E dunit1E ne_x_x1.
byphoare(_ : dt{m1} = dt /\ du{m1} = du ==> _) => //=; proc; seq 1:
  (t = x1) (mu1 dt x1) (mu1 (du x1) x2) _ 0%r true=> //=.
+ by rnd.  
+ by rnd.
+ by hoare; auto=> /> ? ->.
qed.

(* --------------------------------------------------------------------- *)
equiv SampleDep :
  SampleDep.sample ~ SampleDep.sample2 : ={dt, du} ==> res{1} = res{2}.`2.
proof. by proc=> /=; sim. qed.

(* -------------------------------------------------------------------- *)
equiv SampleDLet :
  SampleDLet.sample ~ SampleDLet.sample2 : ={dt, du} ==> res{1} = res{2}.`2.
proof.
bypr (res{1}) (res{2}.`2) => //= &m1 &m2 x [<- <-].
have ->:   Pr[SampleDLet.sample(dt{m1}, du{m1}) @ &m1 : res = x]
         = mu1 (dlet dt{m1} du{m1}) x.
+ by byphoare(_ : dt{m1} = dt /\ du{m1} = du ==> _) => //=; proc; rnd; skip.
suff ->//:   Pr[SampleDLet.sample2(dt{m1}, du{m1}) @ &m2 : res.`2 = x]
           = mu1 (dlet dt{m1} du{m1}) x.
byphoare(_ : dt{m1} = dt /\ du{m1} = du ==> _) => //=.
proc; rnd; skip => /=; rewrite dlet1E dletE_swap /=.
move=> &hr [-> ->]; apply: eq_sum => y /=; rewrite (@sumD1 _ (y, x)) /=.
+ by apply/summable_cond/summableZ/summable_mass. 
rewrite !massE dprod1E dunit1E sum0_eq //=.
case=> y' x' /=; case: (x' = x) => //= ->>.
case: (y' = y) => //= ne_y'y; rewrite !massE dprod1E.
by rewrite dunit1E (@eq_sym y) ne_y'y.
qed.

(* -------------------------------------------------------------------- *)
equiv SampleDepDLet :
  SampleDep.sample ~ SampleDLet.sample : ={dt, du} ==> ={res}.
proof.
transitivity SampleDep.sample2
  (={dt, du} ==> res{1} = res{2}.`2)
  (={dt, du} ==> res{2} = res{1}.`2) => //.
+ by move=> &1 &2 [<- <-]; exists (dt{1}, du{1}).
+ exact SampleDep.
transitivity SampleDLet.sample2
  (={dt, du} ==> ={res})
  (={dt, du} ==> res{2} = res{1}.`2) => //.
+ by move=> &1 &2 [<- <-]; exists (dt{1}, du{1}).
+ exact SampleDepDLet2.
+ symmetry.
conseq (_ : ={dt, du} ==> _); 1: by move=> ?? [<- <-].
exact SampleDLet.
qed.

end DLetSampling.
