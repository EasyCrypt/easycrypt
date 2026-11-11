(* Regression for the equivF_abs oracle-footprint asymmetry.

   `equiv ... proc` for an abstract adversary must require that BOTH oracles
   leave `glob A` unchanged, not only the left one. Here the right oracle O2
   writes the concrete global Shared.g (which an unrestricted `A` may touch, so
   Shared.g in glob A) while the left oracle O1 does not, so the `={glob A}`
   invariant is not preserved by the oracle pair and this equiv is not provable.

   Before the fix `check_oracle_use` was run on the right oracle only when
   o_l = o_r, so the distinct-oracle case silently dropped the obligation and
   the proof below closed (and could be turned into a proof of `false`). With
   the fix the O2 `={glob A}` obligation remains, so the closing `by` must
   fail. *)
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
fail (by proc (true) => //; proc; auto).
abort.
end section.
