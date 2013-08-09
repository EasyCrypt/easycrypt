require import Bool.
require import Int.
require import Map.
require import FSet.
require import List.
require import Fun.
require import Real.

require import AKE_defs.
require import AKE_g0.

pred test_fresh(t : Sid option, evs : Event list) =
  t <> None /\ fresh (proj t) evs.

(* For some small eps to be determined later, we want to prove *)
const eps : real.

lemma Secure:
  forall (A <: Adv) &m,
    2%r * Pr[   AKE(A).main() @ &m : res /\ test_fresh AKE.test AKE.evs] - 1%r < eps
by admit.
