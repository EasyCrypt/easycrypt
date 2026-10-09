(* pHL `while` with an invariant only, upper bound: the bound of the
   conclusion is interpreted in the initial memory, while the goal on the
   loop interprets it in the memory the loop starts from. A bound that
   depends on variables written by the statements preceding the loop must
   be rejected (the judgment below is false for `P.y = -5`). *)
require import AllCore Real.

module P = { var x, y : int  proc p() = { y <- 0; while (x < 1) { x <- x + 1; } } }.

lemma bad : phoare[P.p : true ==> true] <= (P.y%r + 1%r).
proof.
proc.
fail (while (true)).
abort.
