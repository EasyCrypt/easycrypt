(* [proc change] on an ehoare goal: the frame of the local equivalence
   is taken from the boolean part [P] of a precondition [P `|` f]. *)
require import AllCore Xreal.

module M = {
  var x, y : int

  proc f() = {
    M.x <- M.y + 1;
    M.y <- M.x;
  }
}.

lemma L : ehoare [M.f : (M.y = 0) `|` (1%xr) ==> 1%xr].
proof.
proc.
proc change 1 : { M.x <- 1; }.
- (* the frame [M.y{1} = 0] is in the precondition *)
  by auto => /> &1 ->.
by wp; skip => &hr; apply xle_cxr_r.
qed.
