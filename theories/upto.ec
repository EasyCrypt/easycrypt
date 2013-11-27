require import Int.
require import Distr.
require import Real.
require import Pair.
require import Sum.

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

const qO : int.
axiom qO_pos : 0 <= qO.

op def : 'a.

module type Oracle = {
fun f (x : from) : to * bool
}.

module type A (O : Oracle) ={
 fun run () : ret_adv {* O.f}
}.

module Experiment( O : Oracle, AdvF : A) = {
 module WO : Oracle = {
  var cO : int
  var bad : bool
  fun init() : unit = {
   bad = false;
   cO = 0;
  }
  fun f (x : from) : to * bool = { 
   var y : to = def;
   var b : bool = false;
   if (cO < qO /\ !bad) {
    cO = cO + 1;
    (y, b) = O.f(x);
    bad = b ? b : bad;
   }
   return (y, b);
  }
 }
 module Adv = AdvF(WO)
 fun main() : ret_adv = {
  var b : ret_adv = def;
  WO.init();
  b = Adv.run();
  return b;
 }
}.

lemma Conclusion &m p:
forall (O1 <: Oracle{Experiment})(O2 <: Oracle{Experiment}) 
       (Adv <: A{Experiment, O1, O2}),
forall I P,
(0%r <= p <= 1%r) =>
(equiv [O1.f ~ O2.f : I (glob O1){1} (glob O2){2} ==> 
                   ! snd(res){2} => fst res{1} = fst res{2} /\ snd res{1} = snd res{2} 
                                    /\ I (glob O1){1} (glob O2){2}]) =>
(bd_hoare [O2.f : true ==> snd res] <= p ) =>
islossless O1.f =>
islossless O2.f =>
(forall (O <: Oracle{Adv}), islossless O.f => islossless Adv(O).run) =>
I (glob O1){m} (glob O2){m} =>
Pr [Experiment(O1, Adv).main() @ &m : P res] <=
Pr [Experiment(O2, Adv).main() @ &m : P res]  + qO%r * p.
proof.
intros => O1 O2 Adv I P hp hequiv hbound_bad hll1 hll2 hlladv hIm.
apply (Real.Trans _ 
(Pr [Experiment(O2, Adv).main() @ &m : P res \/ (Experiment.WO.bad /\
                          Experiment.WO.cO <= qO)]) _).
equiv_deno (_ : I (glob O1){1} (glob O2){2} ==> 
          (! Experiment.WO.bad{2} => ={res}) /\ Experiment.WO.cO{2} <= qO).
fun.
call (_ : Experiment.WO.bad,
          I  (glob O1){1} (glob O2){2} /\ 
          ={Experiment.WO.cO, Experiment.WO.bad} /\
          Experiment.WO.cO{2} <= qO,
         Experiment.WO.cO{2} <= qO ) => //.
 fun.
 by sp; if => //; wp; call hequiv; wp; skip; progress => //; smt.
 by intros => &2 h; fun; sp; if => //; wp; call hll1; wp; skip; smt.
 by intros => &1; fun; sp; if => //; wp; call hll2; wp; skip; smt.
 by inline Experiment(O1,Adv).WO.init Experiment(O2,Adv).WO.init; wp; 
 skip; progress; smt.
 smt.
 smt.
apply (Real.Trans _ 
(Pr [Experiment(O2, Adv).main() @ &m : P res]  +
Pr [Experiment(O2, Adv).main() @ &m : Experiment.WO.bad /\
                          Experiment.WO.cO <= qO]) _).
rewrite Pr mu_or.
apply (_ : forall (p q r : real), 0%r <= r => p + q - r <= p + q); smt.
apply (_ : forall (a b c : real), b <= c => a + b <= a + c); first smt.
fel 2 Experiment.WO.cO (lambda x,  p)  qO (Experiment.WO.bad) 
 [Experiment(O2,Adv).WO.f : 
  (! Experiment.WO.bad /\ Experiment.WO.cO < qO)] => //. 
 admit. (* sum 0 (n-1) p = n * p *)
 progress.
 by inline Experiment(O2, Adv).WO.init; wp.
 fun.
 sp; if => //; wp; last first.
  hoare; progress; first smt.
  by skip; progress.
 by call hbound_bad; wp; skip; progress; smt.
 by progress; fun; sp; if => //; wp; call (_ : true); wp; skip; progress; smt.
 by progress; fun; sp; if => //; wp; call (_ : true); wp; skip; progress; smt.
save.
