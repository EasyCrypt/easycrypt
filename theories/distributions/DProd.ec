(* -------------------------------------------------------------------- *)
require import AllCore List StdOrder Distr StdOrder.
(*---*) import RealOrder RealSeries StdBigop.Bigreal BRA.

pragma +implicits.

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
proc=> /=; rnd : 0 0; auto => /> &2.
by rewrite -dprod_dlet dmap_id => />; case.
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
lemma dletdepE ['a 'b] (da : 'a distr) (db : 'a -> 'b distr) :
  dlet da (fun a => dmap (db a) (fun b => (a, b))) =
  dlet da (fun a => dunit a `*` db a).
proof.
apply: eq_dlet => // a; rewrite dprodC dprod_dlet dmap_dlet.
by apply: eq_dlet => // b /=; rewrite dlet_unit /= dmap_dunit.
qed.

equiv SampleDepDLet2 :
  SampleDep.sample2 ~ SampleDLet.sample2 : ={dt, du} ==> ={res}.
proof.
proc; rnd : 0 0; auto => /> &2.
by rewrite -dletdepE dmap_id => />; case.
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
proc; rnd; auto=> />; rewrite dlet1E dlet_muE_swap /=.
apply: eq_sum => y /=; rewrite (@sumD1 _ (y, x)) /=.
+ by apply/summable_cond/summableZ/summable_mu1. 
rewrite dprod1E dunit1E sum0_eq //=.
case=> y' x' /=; case: (x' = x) => //= ->>.
case: (y' = y) => //= ne_y'y; rewrite dprod1E.
by rewrite dunit1E (@eq_sym y) ne_y'y.
qed.

(* -------------------------------------------------------------------- *)
equiv SampleDepDLet :
  SampleDep.sample ~ SampleDLet.sample : ={dt, du} ==> ={res}.
proof.
proc; rnd : *0 *0 => /=; auto=> /> &2.
suff ->:
    dlet dt{2} (fun (t : t) => dmap (du{2} t) (fun (u0 : u) => u0))
  = dlet dt{2} du{2}
  by rewrite dmap_id => />.
by apply: eq_dlet => // t; rewrite dmap_id.
qed.

end DLetSampling.
