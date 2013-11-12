require import FSet.
require import Real.
require import Distr.

require import Monoid.
require import ISet.
require import Pair.

theory Mean.
  type input.
  type output.

  op d : input distr.
  
  module type Worker = {
    fun work(x:input) : output
  }.

  module Rand(W:Worker) = {
    fun randAndWork() : input * output = {
      var x : input;
      var r : output;

      x = $d;
      r = W.work(x);
      return (x,r);
    }
  }.

  lemma prCond (A <: Worker {Rand}) &m (v:input)
               (ev:input -> glob A -> output -> bool):
      Pr[Rand(A).randAndWork() @ &m: ev v (glob A) (snd res) /\ v = fst res] =
        (mu_x d v) * Pr[A.work(v) @ &m : ev v (glob A) res].
  proof strict.
  bdhoare_deno (_: (glob A) = (glob A){m} ==> 
                   ev (fst res) (glob A) (snd res) /\ fst res = v) => //.
  pose pr := Pr[A.work(v) @ &m: ev v (glob A) res];
  conseq* (_: _: = (mu_x d v * pr)). (* WEIRD! *)
  fun; seq 1 : (v = x) (mu_x d v) pr 1%r 0%r ((glob A)=(glob A){m})=> //.
    by rnd.
    by rnd; skip; progress=> //; rewrite /mu_x; apply mu_eq.
    call (_: (glob A) = (glob A){m} /\ x = v ==> 
             ev v (glob A) res) => //.
    simplify pr; bypr => &m' eqGlob.
    by equiv_deno (_: ={glob A, x} ==> ={res, glob A}) => //; fun true. 
    by conseq* (_: _ ==> false)=> //.
  qed.

  lemma introOrs (A <: Worker {Rand}) &m (ev:input -> glob A -> output -> bool):
    Finite.finite (create (support d)) =>
    let sup = Finite.toFSet (create (support d)) in
    Pr[Rand(A).randAndWork() @ &m: ev (fst res) (glob A) (snd res)] =
     Pr[Rand(A).randAndWork() @ &m:
          cpOrs (img (lambda v r, ev v (glob A) (snd r) /\ v = fst r) sup) res].
  proof strict.
  intros=> Fsup sup.
  equiv_deno (_: ={glob A} ==> ={glob A, res} /\ in_supp (fst res{1}) d)=> //;
    first by fun; call (_: true); rnd.
  intros=> &m1 &m2 [[<- <-] Hin].
  rewrite /cpOrs or_exists;split.
    intros=> H.
    exists (lambda r, 
              ev (fst res{m1}) (glob A){m1} (snd r) /\ (fst res{m1}) = fst r).
    split=> //. 
    by rewrite img_def; exists (fst (res{m1})); smt.
    by intros=> [x]; rewrite img_def => /= [[v [<- /= Hm] [H1 <- ]]].
  qed.

  lemma Mean (A <: Worker {Rand}) &m (ev:input -> glob A -> output -> bool): 
    Finite.finite (create (support d)) =>
    let sup = Finite.toFSet (create (support d)) in
    Pr[Rand(A).randAndWork()@ &m: ev (fst res) (glob A) (snd res)] =
     Mrplus.sum
       (lambda (v:input), mu_x d v * Pr[A.work(v)@ &m:ev v (glob A) res]) 
       sup.
  proof strict.
  intros=> Fsup /=.
  cut:= introOrs A &m ev _=> //= ->.
  elim/set_ind (Finite.toFSet (create (support d))).
    rewrite Mrplus.sum_empty.
    bdhoare_deno (_ : true ==> false)=> //.
    by rewrite /cpOrs img_empty Mbor.sum_empty.
    intros=> x s Hx Hrec.
    rewrite Mrplus.sum_add //=.
    cut ->: Pr[Rand(A).randAndWork() @ &m:
                 cpOrs (img (lambda (v : input) (r : input * output),
                               ev v (glob A) (snd r) /\ v = fst r) (add x s)) res] =
             Pr[Rand(A).randAndWork() @ &m:
                 (ev x (glob A) (snd res) /\ x = fst res) \/
                 cpOrs (img (lambda (v : input) (r : input * output),
                               ev v (glob A){hr} (snd r) /\ v = fst r) s) res].
      rewrite Pr mu_eq => // &m1.
      pose f:= (lambda (v : input) (r : input * output),
                  ev v (glob A){m1} (snd r) /\ v = fst r).
      rewrite img_add.
      (* bug rewrite cpOrs_add: we are trying to rewrite a partially applied function *)
      cut ->: cpOrs (add (f x) (img f s)) == (cpOr (f x) (cpOrs (img f s))); last by smt.
      by rewrite cpOrs_add.       
    rewrite Pr mu_disjoint; first by smt.
    by rewrite Hrec (prCond A &m x ev).
  qed.
end Mean.
