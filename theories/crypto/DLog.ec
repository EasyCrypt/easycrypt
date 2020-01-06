(* --------------------------------------------------------------------
 * Copyright (c) - 2016--2017 - Roberto Metere (r.metere2@ncl.ac.uk)
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)
 
(* A formalisation of the discrete logarithm assumption. *)

require import CyclicGroup.
require import Real.

theory DLog.

  (* This is the standard definition of discrete logarithm experiment *)
  module type StdAdversary = {
    proc guess(h : group) : F.t
  }.

  module DLogStdExperiment(A:StdAdversary) = {
    proc main () : bool = {
      var x, x';

      x =$ FDistr.dt;
      x' = A.guess(g^x);

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
    proc guess(h : group) : F.t option
  }.

  module DLogExperiment(A:Adversary) = {
    proc main () : bool = {
      var x, x';

      x =$ FDistr.dt;
      x' = A.guess(g^x);
      return (x' = Some x);
    }
  }.
  
end DLog.

(*
  Reduction of the experiment admitting failure to the standard DLog experiment.
*)
section DLogSecurity.

  declare module L:DLog.Adversary.

  module StdRedAdversary(L:DLog.Adversary) = {
    proc guess(h: group) : F.t = {
      var lx, x;

      lx = L.guess(h);
      if (lx = None)
        x =$ FDistr.dt; (* the best if L gave up *)
      else
        x = oget lx;

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
    auto => />; apply FDistr.dt_ll.
  qed.

end section DLogSecurity.
