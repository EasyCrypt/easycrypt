require import Int Real NewDistr List FSet.
require import DInterval.

require (*--*) Dice_sampling.

clone Dice_sampling as D4_6 with
  type t <- int,
  type input <- unit,
  op valid <- predT,
  op d (i:unit) <- [1..6],
  op test (i:unit) <- oflist (range 1 5),
  type t' <- int,
  op d' (i:unit) <- [1..4]
  proof *.
realize valid_nonempty. smt. qed.
realize dU. smt. qed.
realize test_in_d. smt. qed.
realize d'_uni.
  rewrite cardE -(perm_eq_size _ _ (oflistK _)) undup_id 1:range_uniq size_range max_ler //=.
  by move=> x; rewrite support_dinter mux_dinter=> ->.
qed.

module D4 = {
  proc sample () : int = {
    var r : int;
    r = $[1..4];
    return r;
  }
}.

lemma prD4 : forall k &m, Pr[D4.sample() @ &m : res = k] =
   if 1 <= k && k <= 4 then 1%r/4%r else 0%r.
proof.
  move=> k &m; byphoare=> //.
  proc; rnd; skip; progress => //.
  by rewrite -/(pred1 _) -/(mu_x _ _); rewrite mux_dinter.
qed.

module D6 = {
  proc sample () : int = {
    var r : int;
    r = 5;
    while (5 <= r) r = $[1..6];
    return r;
  }
}.

equiv D4_Sample : D4.sample ~ D4_6.Sample.sample : true ==> ={res}.
proof. proc; rnd => //. qed.

equiv D6_RsampleW : D6.sample ~ D4_6.RsampleW.sample : r{2} = 5 ==> ={res}.
proof.
  proc; while (={r}).
    by rnd; skip; smt.
  by auto; rewrite mem_oflist mem_range.
qed.


lemma D4_D6 (f finv : int -> int) :
    (forall i, 1 <= i <= 4 <=> 1 <= f i <= 4) =>
    (forall i, 1 <= i <= 4 => f (finv i) = i /\ finv (f i) = i) =>
    equiv [D4.sample ~ D6.sample : true ==> res{1} = finv res{2}].
proof.
  move=> Hbound Hbij.
  transitivity D4_6.Sample.sample (true ==> ={res}) (true ==> res{1} = finv res{2}) => //.
    by apply D4_Sample.
  transitivity D4_6.RsampleW.sample (r{2} = 5 ==> res{1} = finv res{2})
      (r{1} = 5 ==> res{2} = res{1}) => //.
    by move=> _ _ _;exists ((),5).
    conseq [-frame] (D4_6.Sample_RsampleW f finv) => //.
    move=> &m1 &m2 -> /=; split; first by smt.
    split; first by rewrite mem_oflist mem_range.
    split; first by rewrite weight_dinter.
    split; first by move=> x; rewrite support_dinter mem_oflist mem_range (IntExtra.ltzS _ 4); exact/Hbound.
    split; first by move=> x; rewrite mem_oflist mem_range (IntExtra.ltzS _ 4)=> Hx; cut:= Hbij x _.
    by move=> x; rewrite support_dinter => Hx; cut:= Hbij x _.
  by symmetry; apply/D6_RsampleW.
qed.

lemma prD6 : forall k &m, Pr[D6.sample() @ &m : res = k] =
      if 1 <= k && k <= 4 then 1%r/4%r else 0%r.
proof.
  move=> k &m.
  rewrite -(_:Pr[D4.sample() @ &m : res = k] = Pr[D6.sample() @ &m : res = k]).
    by byequiv (D4_D6 (fun x, x) (fun x, x) _ _).
  by apply (prD4 k &m).
qed.
