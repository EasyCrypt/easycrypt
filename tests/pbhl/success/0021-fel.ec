require import Int.
require import Real.
require import Map.



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

module O : O = {
  var bad : bool
  var counter : int
  var m : (from, to) map

  fun init() : unit = {
    bad = false;
    m = empty;
    counter = 0;
  }

  fun o(x:from) : to = {
    var y : to;
    var r : to;
    if (counter < qO) {
      counter = counter + 1;
      y = $dsample;
      if (in_rng y m) bad = true;
      if (!in_dom x m) {
        m.[x] = y;
      }
      r = proj (m.[x]);
    } else {
      r = default;
    }
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


lemma test : forall (A<:Adv), forall &m,
Pr[M(A).main() @ &m : O.bad /\ O.counter <= qO] <= qO%r * (qO-1)%r * bd.
intros A &m.
fel 1 (O.counter) bd qO (O.bad) (O.counter < qO).
(* *)
smt.
(* *)
trivial.
call ( _ : true ==> !O.bad /\ O.counter = 0);
  [fun;wp; skip; trivial| skip; trivial].
(* with probability reasoning *)
  admit.
(* *)
intros c; fun.
if; [wp;rnd;wp;skip;smt|wp;skip;smt].
(* *)
intros b c;fun.
if; [wp;rnd;wp;skip;smt|wp;skip;smt].
save.




