(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore OldMonoid Finite FSet Distr.

type input.
type output.

op d : input distr.

module type Worker = {
  proc work(x:input) : output
}.

module Rand (W:Worker) = {
  proc main() : input * output = {
    var x : input;
    var r : output;

    x <$ d;
    r <@ W.work(x);
    return (x,r);
  }
}.

lemma prCond (A <: Worker) &m (v:input)
             (ev:input -> glob A -> output -> bool):
    Pr[Rand(A).main() @ &m: ev v (glob A) (snd res) /\ v = fst res] =
      (mu1 d v) * Pr[A.work(v) @ &m : ev v (glob A) res].
proof.
byphoare (_: (glob A) = (glob A){m} ==>
                 ev (fst res) (glob A) (snd res) /\ fst res = v) => //.
pose pr := Pr[A.work(v) @ &m: ev v (glob A) res];
conseq (_: _: = (mu1 d v * pr)). (* WEIRD! *)
proc; seq 1 : (v = x) (mu1 d v) pr 1%r 0%r ((glob A)=(glob A){m})=> //.
+ by rnd.
+ by rnd; skip; progress; rewrite pred1E. 
+ call (_: (glob A) = (glob A){m} /\ x = v ==>
           ev v (glob A) res) => //.
  simplify pr; bypr => &m' eqGlob.
  by byequiv (_: ={glob A, x} ==> ={res, glob A}) => //; proc true.
by hoare; rewrite /fst /snd /=; call (_: true); auto; progress; rewrite eq_sym H.
qed.

lemma introOrs (A <: Worker) &m (ev:input -> glob A -> output -> bool):
  is_finite (support d) =>
  let sup = oflist (to_seq (support d)) in
  Pr[Rand(A).main() @ &m: ev (fst res) (glob A) (snd res)] =
   Pr[Rand(A).main() @ &m:
        cpOrs (image (fun v r, ev v (glob A) (snd r) /\ v = fst r) sup) res].
proof strict.
move=> Fsup sup.
byequiv (_: ={glob A} ==> ={glob A, res} /\ (fst res{1}) \in d)=> //;
  first by proc; call (_: true); rnd.
move=> &m1 &m2 [[<- <-] Hin].
rewrite /cpOrs or_exists;split.
  move=> H.
  exists (fun r,
            ev (fst res{m1}) (glob A){m1} (snd r) /\ (fst res{m1}) = fst r).
  split=> //.
  by rewrite imageP; exists (fst (res{m1})); smt.
  by move=> [x]; rewrite imageP => /= -[[v] /= [Hm <-] /= [h1 <-]].
qed.

lemma Mean (A <: Worker) &m (ev:input -> glob A -> output -> bool):
  is_finite (support d) =>
  let sup = oflist (to_seq (support d)) in
  Pr[Rand(A).main()@ &m: ev (fst res) (glob A) (snd res)] =
   Mrplus.sum
     (fun (v:input), mu1 d v * Pr[A.work(v)@ &m:ev v (glob A) res])
     sup.
proof.
move=> Fsup /=.
have:= introOrs A &m ev _=> //= ->.
elim/fset_ind (oflist (to_seq (support d))).
  rewrite Mrplus.sum_empty.
  byphoare (_ : true ==> false)=> //.
  by rewrite /cpOrs image0 Mbor.sum_empty.
  move=> x s Hx Hrec.
  rewrite Mrplus.sum_add //=.
  have ->: Pr[Rand(A).main() @ &m:
                cpOrs (image (fun (v : input) (r : input * output),
                              ev v (glob A) (snd r) /\ v = fst r) (s `|` fset1 x)) res] =
            Pr[Rand(A).main() @ &m:
                (ev x (glob A) (snd res) /\ x = fst res) \/
                cpOrs (image (fun (v : input) (r : input * output),
                              ev v (glob A){hr} (snd r) /\ v = fst r) s) res].
    rewrite Pr[mu_eq] => // &m1.
    pose f:= (fun (v : input) (r : input * output),
                ev v (glob A){m1} (snd r) /\ v = fst r).
    by rewrite imageU image1 cpOrs_add /predU /f.
  rewrite Pr[mu_disjoint].
  + move=> /> &hr; rewrite negb_and negb_and.
    case: (x = res{hr}.`1)=> //= ->>. 
    case: (ev res{hr}.`1 (glob A){hr} res{hr}.`2)=> //= hev.
    move: Hx=> {Hrec}; elim/fset_ind: s.
    + by rewrite image0 cpOrs0.
    move=> x s x_notin_s ih; rewrite in_fsetU in_fset1 negb_or eq_sym=> - [] /ih.
    by rewrite imageU image1 cpOrs_add /= /predU=> -> ->.
  by rewrite Hrec (prCond A &m x ev).
qed.

lemma Mean_uni (A<:Worker) &m (ev:input -> glob A -> output -> bool) r:
   (forall x, x \in d => mu1 d x = r) =>
   is_finite (support d) =>
   let sup = oflist (to_seq (support d)) in
   Pr[Rand(A).main()@ &m: ev (fst res) (glob A) (snd res)] =
     r * Mrplus.sum (fun (v:input), Pr[A.work(v)@ &m:ev v (glob A) res]) sup.
proof.
  move=> Hd Hfin /=.
  have := Mean A &m ev => /= -> //.
  have := Mrplus.sum_comp (( * ) r) (fun (v:input), Pr[A.work(v)@ &m:ev v (glob A) res]) => /= <-.
    by move=> x y;ringeq.
  apply Mrplus.sum_eq => /= x.
  by rewrite mem_oflist mem_to_seq// /support=> Hin; rewrite Hd.
qed.
