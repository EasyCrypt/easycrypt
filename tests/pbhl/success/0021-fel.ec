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

module type O = {
  fun o(x:from) : to
}.

module type Adv(Foo : O) = {
  fun g() : unit
}.

require import List.

module O : O = {
  var bad : bool
  var m : (from, to) map
  var s : to list

  fun init() : unit = {
    bad = false;
    m = Map.empty;
    s = [];
  }

  fun o(x:from) : to = {
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

  fun main () : unit = {
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
(*   (mu dsample (lambda (z : to), FSet.mem z s)) ((card s)%r * bd). *)

axiom distr_ax :
  forall (s: to list),
  (mu dsample (lambda (z : to), mem z s)) = ((length s)%r * bd).

lemma test : forall (A<:Adv{O}), forall &m,
Pr[M(A).main() @ &m : O.bad /\ (length O.s) <= qO] <= qO%r * (qO-1)%r * bd.
intros A &m.
fel 1 (length O.s) (lambda x, (x%r)*bd) qO O.bad [O.o : (length O.s < qO /\ x=x)].

  (* subgoal on sum *)
  admit.
  (* event holds as postcondition *)
  trivial.
  (* initialization of bad and counter *)
  inline O.init; wp; skip; smt.
  (* sugoals for oracle o *)

  (** pr of setting bad *)
  fun.
  if;[|conseq (_ : _ : = 0%r);[smt|hoare;wp; skip; smt]]. 
  wp.
  simplify.
  rnd (lambda z, mem z O.s).
  skip; simplify.
  intros &hr H.
   rewrite distr_ax.
   smt.

   (** counter increases *)
   intros c.
   fun.
   if;[wp;rnd;skip;smt|wp; skip; smt].

   (** last subgoal for oracle *)
   intros b c.   
   fun.
   if; [wp;rnd;skip;smt|wp; skip; trivial].
save.






