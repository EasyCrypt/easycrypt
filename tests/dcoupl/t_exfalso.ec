(* exfalso: close any dcoupl goal whose precondition is contradictory. *)
require import AllCore Distr.

module M = {
  var a : int
  proc f() : int = { M.a <- 1; return M.a; }
  proc g() : int = { M.a <- 2; return M.a; }
}.

lemma exfalso_false_pre : equiv[ M.f ~ M.g : false ==> ={M.a} ].
proof.
proc. delay.
dcoupl exfalso. smt().
qed.

lemma exfalso_contradictory_pre :
  equiv[ M.f ~ M.g : M.a{1} = 0 /\ M.a{1} = 1 ==> ={M.a} ].
proof.
proc. delay.
dcoupl exfalso. smt().
qed.

(* exfalso only discharges the goal when the pre is contradictory. *)
lemma exfalso_satisfiable_pre : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
dcoupl exfalso.
(* Remaining goal: forall &1 &2, true => false. *)
admit.
qed.
