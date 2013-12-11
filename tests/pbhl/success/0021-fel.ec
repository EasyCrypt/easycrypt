require import Int.
require import Real.
require import Map. 
require import FSet.


type from.
type to.

op dsample : to distr. (* Distribution to use on the target type *)
op qO : int.           (* Maximum number of calls by the adversary *)
op default : to.       (* Default element to return on error by wrapper *)

op bd : real.
axiom bdPos : bd >= 0%r.

module type O = {
  proc o(x:from) : to
}.

module type Adv(Foo : O) = {
  proc g() : unit
}.

require import List.

module O : O = {
  var bad : bool
  var m : (from, to) map
  var s : to list

  proc init() : unit = {
    bad = false;
    m = Map.empty;
    s = [];
  }

  proc o(x:from) : to = {
    var y : to;
    var r : to;

    if (length s < qO ) {
      y = $dsample;
      if (List.mem y s) bad = true;
      if (!in_dom x m) m.[x] = y;
      s = y :: s;
    }
    r = proj (m.[x]);
    return r;
  }
}.
 

module M(A:Adv)  = {
  module AO = A(O)

  proc main () : unit = {
    O.init();
    AO.g();
  }

}
.

require import Sum.
axiom qO_pos : 0 < qO.

require import Distr.

(* BUG: this returns a weird error message *) 
(* axiom distr_ax : *)
(*   forall (s: to set), *)
(*   (mu dsample (fun (z : to), FSet.mem z s)) ((card s)%r * bd). *)

axiom distr_ax :
  forall (s: to list),
  (mu dsample (fun (z : to), mem z s)) = ((length s)%r * bd).

lemma test : forall (A<:Adv{O}), forall &m,
Pr[M(A).main() @ &m : O.bad /\ (length O.s) <= qO] <= qO%r * (qO-1)%r * bd.
intros A &m.
fel 1 (length O.s) (fun x, (x%r)*bd) qO O.bad [O.o : (length O.s < qO /\ x=x)].

  (* subgoal on sum *)
  rewrite /int_sum /intval (_:qO=qO-1+1);first smt.
  elim/Induction.induction (qO-1);last smt.
    cut h1 : (0 <= 0 + 1 - 1);first smt.
    cut h2 : (0 > 0 + 1 - 1 - 1);first smt.
    by rewrite Interval.interval_pos // Interval.interval_neg //
      MReal.SumSet.sum_add ? mem_empty // MReal.SumSet.sum_nil;smt.
    intros=> i h hrec.
    cut h1 : 0 <= i + 1 + 1 - 1 by smt.
    cut h2 : ! 0 <= i + 1 + 1 - 1 <= i + 1 + 1 - 1 - 1 by smt.
    cut h3 : i + 1 + 1 - 1 - 1=i+1-1 by smt.
    by rewrite Interval.interval_pos // MReal.SumSet.sum_add ?
      Interval.mem_interval // h3;smt.
  (* event holds as postcondition *)
  trivial.
  (* initialization of bad and counter *)
  inline O.init; wp; skip; smt.
  (* sugoals for oracle o *)

  (** pr of setting bad *)
  proc.
  if;[|conseq (_ : _ : = 0%r);[smt|hoare;wp; skip; smt]]. 
  wp.
  simplify.
  rnd (fun z, mem z O.s).
  skip; simplify.
  intros &hr H.
   rewrite distr_ax.
   smt.

   (** counter increases *)
   intros c.
   proc.
   if;[wp;rnd;skip;smt|wp; skip; smt].

   (** last subgoal for oracle *)
   intros b c.   
   proc.
   if; [wp;rnd;skip;smt|wp; skip; trivial].
qed.






