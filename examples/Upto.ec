(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Int Real Distr StdOrder StdBigop.
(*---*) import RealOrder Bigreal BRA.
require (*--*) FelTactic.

(* Simple up to bad reasoning *)
(* Scenario: you have an adversary with access to an oracle f
   and exactly q calls to it.
   You replace the oracle f with oracle f' and you know that
   f and f' return the same result with probability p. Then,
   you can conclude that the probability of distinguishing is
   q * p *)

type from.
type to.

type ret_adv.

op qO : { int | 0 <= qO } as qO_pos.

op def : 'a.

module type Oracle = {
  proc init () : unit
  proc f (x : from) : to * bool
}.

module type A (O : Oracle) ={
  proc * run () : ret_adv { O.f}
}.

module Experiment (O : Oracle) (AdvF : A) = {
  module WO : Oracle = {
    var cO : int
    var bad : bool

    proc init() : unit = {
      bad <- false;
      cO  <- 0;
      O.init();
    }

    proc f (x : from) : to * bool = {
      var y <- def;
      var b <- false;

      if (cO < qO /\ !bad) {
        cO     <- cO + 1;
        (y, b) <@ O.f(x);
        bad    <- b ? b : bad;
      }
      return (y, b);
    }
  }

  proc main() : ret_adv = {
    var b <- def;

    WO.init();
    b <@ AdvF(WO).run();
    return b;
  }
}.

(* TODO: wut? Document this. *)
lemma Conclusion &m p
                 (O1 <: Oracle{Experiment})(O2 <: Oracle{Experiment})
                 (Adv <: A{Experiment, O1, O2})
                 I P (m : glob O2 -> int) (g : int -> real):
  (forall x, 0%r <= g x <= 1%r) =>
  bigi predT g 0 qO <= qO%r * p =>
  (equiv [O1.init ~ O2.init: true ==>
                     I (glob O1){1} (glob O2){2} /\
                     (m (glob O2)){2} = 0 ]) =>
  hoare [ O2.init : true ==> m (glob O2) = 0 ] =>
  (forall k,
     equiv [O1.f ~ O2.f : I (glob O1){1} (glob O2){2} /\
                          (m ( glob O2)){2} = k ==>
                          (m (glob O2)){2} = k + 1 /\
                          (! snd(res){2} => fst res{1} = fst res{2} /\
                                            snd res{1} = snd res{2} /\
                                            I (glob O1){1} (glob O2){2})]) =>
  (forall k,
     hoare [O2.f : (m (glob O2)) = k ==>
                   (m (glob O2)) = k + 1]) =>
  (forall k,
     phoare [O2.f : m (glob O2) = k ==> snd res] <= (g k )) =>
  islossless O1.f =>
  islossless O2.f =>
  (forall (O <: Oracle{Adv}), islossless O.f => islossless Adv(O).run) =>
  I (glob O1){m} (glob O2){m} =>
  Pr [Experiment(O1, Adv).main() @ &m : P res]
  <= Pr [Experiment(O2, Adv).main() @ &m : P res]  + qO%r * p.
proof.
move=> hg hbnd hinint hinit2 hf hf2 hbound_bad hll1 hll2 hlladv hIm.
apply (ler_trans (Pr [Experiment(O2, Adv).main() @ &m : P res \/ (Experiment.WO.bad /\
                                                                  Experiment.WO.cO <= qO /\
                                                                  Experiment.WO.cO = m (glob O2))]) _).
+ byequiv (: true ==>
             (!Experiment.WO.bad{2} => ={res}) /\
              Experiment.WO.cO{2} <= qO /\
              Experiment.WO.cO{2} = m (glob O2){2})=> //.
  + proc.
    call (: Experiment.WO.bad,
            I  (glob O1){1} (glob O2){2} /\
            ={Experiment.WO.cO, Experiment.WO.bad} /\
            Experiment.WO.cO{2} <= qO /\
            Experiment.WO.cO{2} = m (glob O2){2},
            Experiment.WO.cO{2} <= qO /\
            Experiment.WO.cO{2} = m (glob O2){2})=> // {g hg hbnd hbound_bad}.
    + proc; sp; if=> //.
      swap 1 2; wp.
      exists * (Experiment.WO.cO{2}); elim * => cO.
      by call (hf cO); auto => /> /#.
    + by move=> /> &2 h; proc; sp; if=> //; wp; call hll1; auto.
    + by move=> />; proc; sp; if => //; wp; call hll2; auto.
    inline Experiment(O1,Adv).WO.init Experiment(O2,Adv).WO.init; wp.
    by call hinint; auto=> />; smt(qO_pos).
  smt().
apply (ler_trans (Pr [Experiment(O2, Adv).main() @ &m : P res]  +
                  Pr [Experiment(O2, Adv).main() @ &m :
                         Experiment.WO.bad /\
                         Experiment.WO.cO <= qO /\
                         Experiment.WO.cO = m (glob O2){hr}]) _).
+ by rewrite Pr [mu_or]; smt(ge0_mu).
apply (: forall (a b c : real), b <= c => a + b <= a + c).
+ smt(ge0_mu).
fel 2 Experiment.WO.cO g qO (Experiment.WO.bad)
    [Experiment(O2,Adv).WO.f : (!Experiment.WO.bad  /\ Experiment.WO.cO < qO)]
    (m (glob O2) = Experiment.WO.cO)=> //.
+ by inline Experiment(O2, Adv).WO.init; call hinit2; auto.
+ proc; sp 2; if=> //; wp; last first.
  + by hoare; auto=> /#.
  swap 1 1; wp.
  exists* Experiment.WO.cO; elim* => cO.
  conseq (: _ : (g cO))=> //.
  exists* Experiment.WO.bad; elim* => b.
  by call (hbound_bad cO); auto.
+ move=> c; proc; sp; if=> //; wp.
  exists* Experiment.WO.cO; elim* => cO.
  by call (hf2 cO); auto=> /> /#.
move=> b c; proc; sp; if=> //.
swap 1 1; wp.
exists* Experiment.WO.cO; elim* => cO.
by call (hf2 cO); auto=> /> /#.
qed.
