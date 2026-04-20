(* frame: add a Write-disjoint invariant to pre and post. *)
require import AllCore Distr.

module M = {
  var a, b : int
  proc f() : int = { M.a <- 1; return M.a; }
  proc g() : int = { M.a <- 1; return M.a; }
}.

(* Positive case: theta touches only b; body writes only a. *)
lemma frame_ok :
  equiv[ M.f ~ M.g : ={M.a, M.b} ==> true ].
proof.
proc. delay.
dcoupl frame (M.b{1} = M.b{2}).
(* Goal's pre is now (={M.a, M.b}) /\ (={M.b}). *)
dcoupl wp. dcoupl skip. smt().
qed.

(* Negative case: theta touches a, which the body writes. Must fail. *)
lemma frame_bad :
  equiv[ M.f ~ M.g : ={M.a} ==> true ].
proof.
proc. delay.
fail dcoupl frame (M.a{1} = M.a{2}).
admit.
qed.
