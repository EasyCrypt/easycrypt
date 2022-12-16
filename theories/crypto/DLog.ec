(* A formalisation of the discrete logarithm assumption. *)

require (****) Group.
require import Real.

clone Group.CyclicGroup as G.

axiom prime_p : IntDiv.prime G.order.

clone G.PowZMod as GP with
  lemma prime_order <- prime_p.

clone GP.FDistr as FD.

import G GP FD.

theory DLog.

  (* This is the standard definition of discrete logarithm experiment *)
  module type StdAdversary = {
    proc guess(h : group) : exp
  }.

  module DLogStdExperiment(A:StdAdversary) = {
    proc main () : bool = {
      var x, x';

      x  <$ dt;
      x' <@ A.guess(g ^ x);

      return (x' = x);
    }
  }.

  (*
     This is a modified definition in which the adversary may fail.

     In comparison, the standard adversary always tries to provide an answer,
     which may be succesful with probability 1/q, where q grows exponentially
     in the security parameter.
  *)
  module type Adversary = {
    proc guess(h : group) : exp option
  }.

  module DLogExperiment(A:Adversary) = {
    proc main () : bool = {
      var x, x';

      x  <$ FD.dt;
      x' <@ A.guess(g ^ x);
      return (x' = Some x);
    }
  }.

end DLog.

(*
  Reduction of the experiment admitting failure to the standard DLog experiment.
*)
section DLogSecurity.

  declare module L <: DLog.Adversary.

  module StdRedAdversary(L:DLog.Adversary) = {
    proc guess(h: group) : exp = {
      var lx, x;

      lx <@ L.guess(h);
      if (lx = None)
        x <$ dt; (* the best if L gave up *)
      else
        x <- oget lx;

      return x;
    }
  }.

  lemma dlog_standard_reduction &m:
    Pr[DLog.DLogExperiment(L).main() @ &m : res] <=
    Pr[DLog.DLogStdExperiment(StdRedAdversary(L)).main() @ &m : res].
  proof.
    byequiv => //; proc; inline*.
    wp; seq 2 3: (x'{1} = lx{2} /\ x{1} = x{2}).
    + by call (_: true); auto.
    if{2} => //; last by auto.
    auto => />; apply dt_ll.
  qed.

end section DLogSecurity.
