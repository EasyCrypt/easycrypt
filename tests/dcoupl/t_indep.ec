(* indep: remove common T-suffix from R and S when Read/Write disjoint. *)
require import AllCore Distr.

module M = {
  var a, b : int
  proc f() : int = { return M.a; }
  proc g() : int = { return M.a; }
}.

(* indep fires only on the right shape; verify the error path. *)
lemma indep_empty :
  equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
fail dcoupl indep 1 1.  (* R/S are too short *)
admit.
qed.
