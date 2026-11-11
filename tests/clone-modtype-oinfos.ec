(* Regression for #1123: `clone ... with module type X <- Y` must compare the
   oracle-call restrictions of X and Y, not only procedure names and types.
   Lemmas proved for `A <: X` are replayed verbatim for `A <: Y`, so the
   allowed-call sets must coincide exactly (as sets, order-insensitively). *)
require import AllCore.

theory T.
  module type ORCL = { proc g() : unit  proc h() : unit  proc k() : unit }.
  module type ADV (O : ORCL) = { proc f() : unit {O.g, O.h} }.
  module type GAME (A : ADV) = { proc main() : bool }.
end T.

module type ADV_looser  (O : T.ORCL) = { proc f() : unit {O.g, O.h, O.k} }.
module type ADV_tighter (O : T.ORCL) = { proc f() : unit {O.g} }.
module type ADV_reorder (O : T.ORCL) = { proc f() : unit {O.h, O.g} }.

fail clone T as U1 with module type ADV <- ADV_looser.
fail clone T as U2 with module type ADV <- ADV_tighter.
fail clone T as U3 with module type ADV =  ADV_looser.
fail clone T as U4 with module type ADV <= ADV_tighter.

clone T as U5 with module type ADV <- ADV_reorder.

(* The oracle sets of functor parameters' signatures are compared too. *)
module type GAME_looser  (A : ADV_looser)  = { proc main() : bool }.
module type GAME_reorder (A : ADV_reorder) = { proc main() : bool }.

fail clone T as U6 with module type GAME <- GAME_looser.

clone T as U7 with module type GAME <- GAME_reorder.
