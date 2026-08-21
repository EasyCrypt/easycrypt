(* ------------------------------------------------------------------------ *)
(* [eager proc] on an abstract function of module A must enforce that the   *)
(* swapping statement does not modify [glob A].                             *)
(* ------------------------------------------------------------------------ *)
require import AllCore.

module Shared = { var g : int }.

module type T = { proc main() : int }.

section.
declare module A <: T.

lemma bad :
  eager[ Shared.g <- 5;, A.main ~ A.main, Shared.g <- 5; : ={glob A} ==> ={res} ].
proof.
fail (eager proc (true)).
abort.

end section.
