require import Int Real Distr List FSet.
require import DInterval Dexcepted.

pragma +implicits.

clone WhileSamplingFixedTest as D4_6 with
  type t             <- int,
  type input         <- unit,
  op   dt   (i:unit) <- [1..6],
  op   test (i:unit) <- fun r=> !1 <= r <= 4
proof *.

module D4 = {
  proc sample () : int = {
    var r : int;

    r <$ [1..4];
    return r;
  }
}.

lemma prD4 : forall k &m, Pr[D4.sample() @ &m : res = k] =
  if 1 <= k <= 4 then 1%r/4%r else 0%r.
proof.
move=> k &m; byphoare=> //.
by proc; rnd; auto=> />; rewrite dinter1E.
qed.

module D6 = {
  proc sample () : int = {
    var r <- 5;

    while (5 <= r) r <$ [1..6];
    return r;
  }
}.

equiv D4_Sample: D4.sample ~ D4_6.SampleE.sample: true ==> ={res}.
proof.
proc; rnd; auto=> />; split=> [r|_ r].
+ rewrite supp_dexcepted supp_dinter=> /= - [] _ r_bounds.
  rewrite dexcepted1E /= r_bounds /=.
  rewrite weight_dinter /= !dinter1E dinterE size_filter.
  rewrite /range /= (@iotaS 1 5) //= (@iotaS 2 4) //= (@iotaS 3 3) //=.
  rewrite (@iotaS 4 2) //= (@iotaS 5 1) //= (@iotaS 6 0) //= (@iota0 7 0) //=.
  by rewrite /b2i /max /#.
by rewrite supp_dinter supp_dexcepted supp_dinter /= /#.
qed.

equiv D6_Sample: D6.sample ~ D4_6.SampleWi.sample: r{2} = 5 ==> ={res}.
proof.
proc=> /=; while (={r}).
+ by rnd; auto=> /> &2 _ + r; rewrite supp_dinter /#.
by auto.
qed.

lemma D4_D6 (f finv : int -> int) :
    (forall i, 1 <= i <= 4 <=> 1 <= f i <= 4) =>
    (forall i, 1 <= i <= 4 => f (finv i) = i /\ finv (f i) = i) =>
    equiv [D4.sample ~ D6.sample : true ==> res{1} = finv res{2}].
proof.
move=> Hbound Hbij.
transitivity D4_6.SampleE.sample (true ==> ={res})
                                 (true ==> res{1} = finv res{2})=> //.
+ exact/D4_Sample.
transitivity D4_6.SampleWi.sample (r{2} = 5 ==> res{1} = finv res{2})
                                  (r{1} = 5 ==> res{2} = res{1})=> //.
+ by move=> />; exists ((),5).
transitivity D4_6.SampleE.sample (true ==> res{1} = finv res{2})
                                 (r{2} = 5 ==> ={res})=> //.
(* TODO: This is generic and should be extracted in a clean way. *)
+ proc; rnd f finv; auto=> />; split=> [r|_].
  + by rewrite supp_dexcepted supp_dinter /#.
  split=> [r|_ r].
  + rewrite supp_dexcepted supp_dinter=> - /= [] _ r_bounds.
    apply/dexcepted_uni.
    + exact/dinter_uni.
    + by rewrite supp_dexcepted supp_dinter /#.
    by rewrite supp_dexcepted supp_dinter /#.
  by rewrite 2!supp_dexcepted 2!supp_dinter/#.
+ conseq D4_6.sampleE_sampleWi=> //=.
  by move=> &2 ->; rewrite dinter_ll //= /predC mem_oflist mem_range.
by symmetry; exact/D6_Sample.
qed.

lemma prD6 : forall k &m, Pr[D6.sample() @ &m : res = k] =
      if 1 <= k <= 4 then 1%r/4%r else 0%r.
proof.
move=> k &m.
rewrite -(: Pr[D4.sample() @ &m: res = k] = Pr[D6.sample() @ &m: res = k]).
+ by byequiv (D4_D6 (fun x=> x) (fun x=> x) _ _).
exact/(@prD4 k &m).
qed.
