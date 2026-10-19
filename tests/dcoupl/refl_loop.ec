(* Reflexivity of a while-loop procedure via the two-sided dcoupl while.
   Subgoals: (1) tests agree under the invariant, (2) the body preserves
   the invariant, (3) the pre establishes the invariant, (4) the
   invariant and the negated test imply the post.                     *)
require import AllCore Distr.

module M = {
  var a : int
  proc f() : int = {
    while (M.a < 10) { M.a <- M.a + 1; }
    return M.a;
  }
}.

lemma refl_loop : equiv[ M.f ~ M.f : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl while (={M.a}) with ~.
- smt().
- dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
- dcoupl skip. smt().
- dcoupl skip. smt().
qed.
