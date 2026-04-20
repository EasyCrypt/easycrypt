(* cond_l: simplify direction (close a goal matching the conclusion shape). *)
require import AllCore Distr DBool.

module M = {
  var x : bool
  var y : bool
  proc f() : bool = { M.y <- M.x; return M.y; }
  proc g() : bool = { return M.x; }
}.

(* cond_l fires only when the shape matches. Verify shape-check errors. *)
lemma cond_l_shape_empty_R : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
fail dcoupl cond.       (* R is empty *)
admit.
qed.

(* cond_l intro fires only when R_l ends in a sample. Verify error. *)
lemma cond_l_intro_shape_empty_R : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
fail dcoupl cond intro. (* R is empty *)
admit.
qed.
