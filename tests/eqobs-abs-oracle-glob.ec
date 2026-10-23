(* Regression for the eqobs_in / `sim` abstract-oracle glob drop.

   `f_eqobs_in` (FBabs case, ecPhlEqobs.ml) unconditionally added `={glob A}`
   to the inferred invariant of an abstract call, asserting the call preserves
   the adversary's globals without checking the oracle pair. Here the right
   oracle O2 writes the concrete global Shared.g (which unrestricted `A` may
   touch, so Shared.g in glob A) while the left oracle O1 does not, so
   `={glob A}` is NOT preserved and this equiv must not be provable by `sim`.
   Before the fix `proc*; sim` closed it (a proof of `false` followed). *)
require import AllCore.

module Shared = { var g : int }.
module type O = { proc f() : unit }.
module type Adv (M : O) = { proc main() : int }.
module O1 : O = { proc f() : unit = { } }.
module O2 : O = { proc f() : unit = { Shared.g <- Shared.g + 1; } }.

section.
declare module A <: Adv.

lemma bad : equiv[ A(O1).main ~ A(O2).main : ={glob A} ==> ={res} ].
proof.
fail (by proc*; sim).
abort.
end section.
