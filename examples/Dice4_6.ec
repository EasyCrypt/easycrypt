require import Dice_sampling.
import Distr.
import FSet.
import Int.
import Real.

op d6 (i:unit) = [1..6].
op test4 (i:unit) x = 1 <= x <= 4.
op sub_supp (i:unit) = Interval.interval 1 4.
op bd6 = 1%r/6%r.
op d4 (i:unit) = [1..4].

lemma d6_uni: forall (i : unit) (x : int), in_supp x (d6 i) => mu_x (d6 i) x = bd6.
proof.
  intros i x; apply (Distr.Dinter.mu_x_def_in 1 6 x).
save.

lemma test_in_supp: forall (i : unit) (x : int), test4 i x => in_supp x (d6 i).
proof.
  intros i x;rewrite /test4 /d6 Dinter.supp_def;smt.
save.

lemma test_sub_supp: forall (i : unit) (x : int), mem x (sub_supp i) <=> test4 i x.
proof. 
  (*PY: Bug ? *)
(*  intros i x; apply (Interval.mem_interval 1 4). *)
  intros i x;rewrite /sub_supp /test4;apply Interval.mem_interval.
save.

lemma d'_uni: forall (i : unit) (x : int),
           in_supp x (d4 i) => mu_x (d4 i) x = 1%r / (card (sub_supp i))%r.
proof.
  intros i x;rewrite /d4 /sub_supp Interval.card_interval_max /max /=.
  apply (Distr.Dinter.mu_x_def_in 1 4 x).
save.
 
clone GenDice as D4_6 with 
  type t <- int,
  type input <- unit,
  op d <- d6,
  op test <- test4,
  op sub_supp <- sub_supp,
  op bd <- bd6,
  type t' <- int,
  op d' <- d4
  proof * by smt.

module D4 = {
  fun sample () : int = { 
    var r : int;
    r = $[1..4];
    return r;
  }
}.

lemma prD4 : forall k &m, Pr[D4.sample() @ &m : res = k] = 
   if 1 <= k && k <= 4 then 1%r/4%r else 0%r.
proof.
  intros k &m;bdhoare_deno (_: true ==> k = res) => //.
  fun;rnd;skip;progress => //.
  rewrite (_:mu [1..4] (lambda (x : int), k = x) = mu_x [1..4] k).
    by rewrite /mu_x;apply mu_eq.
  by case (1 <= k && k <= 4) => Hk; 
    [rewrite Dinter.mu_x_def_in // | rewrite Dinter.mu_x_def_notin //];
    rewrite Dinter.supp_def. 
save.

module D6 = {
  fun sample () : int = {
    var r : int;
    r = 5;
    while (5 <= r) r = $[1..6];
    return r;
  }
}.

equiv D4_Sample : D4.sample ~ D4_6.Sample.sample : true ==> ={res}.
proof. fun;rnd => //. save.

equiv D6_RsampleW : D6.sample ~ D4_6.RsampleW.sample : r{2} = 5 ==> ={res}.
proof. 
  fun;while (={r}).
    by rnd;skip;progress => //; smt.
  by wp.
save.

lemma D4_D6 (f finv : int -> int) :
    (forall i, 1 <= i <= 4 <=> 1 <= finv i <= 4) =>
    (forall i, 1 <= i <= 4 => f (finv i) = i /\ finv (f i) = i) =>
    equiv [D4.sample ~ D6.sample : true ==> f res{1} = res{2}].
proof.
  intros Hbound Hbij.
  transitivity D4_6.Sample.sample (true ==> ={res}) (true ==> f res{1} = res{2}) => //.
    by apply D4_Sample.
  transitivity D4_6.RsampleW.sample (r{2} = 5 ==> f res{1} = res{2})
      (r{1} = 5 ==> res{2} = res{1}) => //.
    by intros _ _ _;exists 5 => //.
    conseq (D4_6.Sample_RsampleW f finv) => //.
    rewrite /d6 /test4 /d4 => &m1 &m2 -> /=;split; first by smt.
    split; first by rewrite Dinter.weight_def.
    split; first by intros x;rewrite Dinter.supp_def;apply Hbound.
    split; first by intros x Hx;elim (Hbij x _).
    by intros x; rewrite Dinter.supp_def => Hx;elim (Hbij x _).
  by symmetry;apply D6_RsampleW.
save.

lemma prD6 : forall k &m, Pr[D6.sample() @ &m : res = k] = 
      if 1 <= k && k <= 4 then 1%r/4%r else 0%r.
proof.
  intros k &m. 
  rewrite -(_:Pr[D4.sample() @ &m : res = k] = Pr[D6.sample() @ &m : res = k]).
    by equiv_deno (D4_D6 (lambda x, x) (lambda x, x) _ _).
  by apply (prD4 k &m). 
save.
