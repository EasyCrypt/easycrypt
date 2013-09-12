require import Int.
require import Real.
require import Distr.

module G0 = {
  fun main(): int = {
    var x:int;
    x = $[1..4];
    return x;
  }
}.

module G1 = {
  fun main():int = {
    var x:int = 5;

    while (x > 4)
      x = $[1..6];
    return x;
  }
}.

const k:int.

module G2 = {
  var bad:bool

  fun main():int = {
    var x:int = 5;
    var i:int = 0;

    bad = false;
    while (x > 4 /\ i < k)
    {
      x = $[1..6];
      i = i + 1;
    }
    bad = x > 4;

    return x;
  }
}.

(** What we want to prove *)

(* Potential Problems:
   - ensure termination of the while loop (prove that the loop
     invariant entails that the probability of the loop condition
     failing is non-zero);
   - when matching the single sampling wit hthe final iterated
     sampling, the probability in the iterated game needs to be
     normalized by the observation that the sampled variable is
     in the domain of the left distribution. *)
equiv G0_G1: G0.main ~ G1.main: true ==> ={res}.
admit. qed.

(* Potential Problems:
   - The loops are only synchronized until the counter runs out.
     It may be necessary to cut the non-PTIME loop into a countered
     component that is synchronous with the other side, and an unguarded
     component for reasoning after bad is set.
   - We'll therefore probably still need to prove termination using the
     non-zero probability of falsifying the branch condition.
   - Computing the probability of the bad event is not going to be an
     easy task.*)
equiv G1_G2: G1.main ~ G2.main: true ==> !G2.bad{2} => ={res}.
admit. qed.

lemma G2_bad &m: Pr[G2.main() @ &m: G2.bad] = (1%r / 3%r)^k.
admit. qed.