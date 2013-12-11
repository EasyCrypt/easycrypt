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
proc init () : unit
proc f (x : from) : to * bool
}.

module type A (O : Oracle) ={
 proc * run () : ret_adv { O.f}
}.

module Experiment( O : Oracle, AdvF : A) = {
 module WO : Oracle = {
  var cO : int
  var bad : bool
  proc init() : unit = {
   bad = false;
   cO = 0;
   O.init();
  }
  proc f (x : from) : to * bool = { 
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
 proc main() : ret_adv = {
  var b : ret_adv = def;
  WO.init();
  b = Adv.run();
  return b;
 }
}.

lemma Conclusion &m p:
forall (O1 <: Oracle{Experiment})(O2 <: Oracle{Experiment}) 
       (Adv <: A{Experiment, O1, O2}),
forall I P (m : glob O2 -> int) (g : int -> real),
(forall x, 0%r <= g x <= 1%r) =>
int_sum g (intval 0 (qO - 1)) <= qO%r * p =>
(equiv [O1.init ~ O2.init : true ==> 
                   I (glob O1){1} (glob O2){2} /\
                   (m (glob O2)){2} = 0 ]) =>
hoare [ O2.init : true ==> m (glob O2) = 0 ] =>
(forall k, 
equiv [O1.f ~ O2.f : I (glob O1){1} (glob O2){2} /\ 
                      (m ( glob O2)){2} = k ==> 
                    (m (glob O2)){2} = k + 1 /\
                   (! snd(res){2} => fst res{1} = fst res{2} 
                    /\ snd res{1} = snd res{2} 
                    /\ I (glob O1){1} (glob O2){2})]) =>
(forall k, 
hoare [O2.f : (m (glob O2)) = k ==> 
              (m (glob O2)) = k + 1]) =>
(forall k,
 phoare [O2.f : m (glob O2) = k ==> snd res] <= (g k )) =>
islossless O1.f =>
islossless O2.f =>
(forall (O <: Oracle{Adv}), islossless O.f => islossless Adv(O).run) =>
I (glob O1){m} (glob O2){m} =>
Pr [Experiment(O1, Adv).main() @ &m : P res] <=
Pr [Experiment(O2, Adv).main() @ &m : P res]  + qO%r * p.
proof.
intros => O1 O2 Adv I P m g hg hbnd hinint hinit2 hf hf2 hbound_bad hll1 hll2 hlladv hIm.
apply (Real.Trans _ 
(Pr [Experiment(O2, Adv).main() @ &m : P res \/ (Experiment.WO.bad /\
                          Experiment.WO.cO <= qO /\ 
Experiment.WO.cO = m (glob O2))]) _).
equiv_deno (_ : true ==> 
          (! Experiment.WO.bad{2} => ={res}) /\ 
             Experiment.WO.cO{2} <= qO /\
             Experiment.WO.cO{2} = m (glob O2){2})  => //.
proc.
call (_ : Experiment.WO.bad,
          I  (glob O1){1} (glob O2){2} /\ 
          ={Experiment.WO.cO, Experiment.WO.bad} /\
          Experiment.WO.cO{2} <= qO /\
          Experiment.WO.cO{2} = m (glob O2){2},
          Experiment.WO.cO{2} <= qO /\ 
          Experiment.WO.cO{2} = m (glob O2){2}) => // {g hg hbnd hbound_bad}.
 proc.
 sp; if => //.
 swap 1 2; wp.
 exists *(  Experiment.WO.cO{2}).
 elim * => cO.
 call (hf cO); skip; progress => //; smt.
 by intros => &2 h; proc; sp; if => //; wp; call hll1; wp; skip; smt.
 by intros => &1; proc; sp; if => //; wp; call hll2; wp; skip; smt.
 inline Experiment(O1,Adv).WO.init Experiment(O2,Adv).WO.init; wp. 
 call hinint; wp; skip; progress; smt.
smt.
apply (Real.Trans _ 
(Pr [Experiment(O2, Adv).main() @ &m : P res]  +
Pr [Experiment(O2, Adv).main() @ &m : 
             Experiment.WO.bad /\ Experiment.WO.cO <= qO /\ 
             Experiment.WO.cO = m (glob O2){hr}]) _).
rewrite Pr mu_or.
apply (_ : forall (p q r : real), 0%r <= r => p + q - r <= p + q); 
 intros {g hg hbnd hbound_bad}; smt.
apply (_ : forall (a b c : real), b <= c => a + b <= a + c); 
 first (intros {g hg hbnd hbound_bad}; smt).
fel 2 Experiment.WO.cO g  qO (Experiment.WO.bad) 
 [Experiment(O2,Adv).WO.f : 
  (!Experiment.WO.bad  /\ Experiment.WO.cO < qO)]
(m (glob O2) = Experiment.WO.cO) => //. 
by inline Experiment(O2, Adv).WO.init; call hinit2; wp.
 proc.
 sp; if => //; wp; last first.
  hoare; progress; first smt.
  by skip; progress.

swap 1 1; wp.
exists* Experiment.WO.cO.
elim* => cO.
conseq (_ : _ : (g cO)).
progress.
exists* Experiment.WO.bad.
elim* => b.
call (hbound_bad cO); skip; progress; smt.
intros => c.
proc.
sp; if => //; wp.
exists* Experiment.WO.cO.
elim* => cO. 
call (hf2 cO); wp; skip ; progress.
intros => {g hg hbnd hbound_bad}; smt.
intros => {g hg hbnd hbound_bad}; smt.

intros => b c.
proc; sp; if => //.
swap 1 1; wp.
exists* Experiment.WO.cO.
elim* => cO. 
call (hf2 cO); wp; skip ; progress; smt.
qed.
