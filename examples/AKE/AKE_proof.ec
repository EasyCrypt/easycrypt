require import Bool.
require import Int.
require import Map.
require import FSet.
require import List.
require import Fun.
require import Real.

require import AKE_defs.
require import AKE_g0.

const eps : real.

lemma Correct:
  forall (A <: Adv) &m,
    2%r * Pr[ AKE(A).main() @ &m : res /\ AKE.test <> None /\ (fresh (proj AKE.test) AKE.evs) ] - 1%r < eps.