(* case: split on a predicate and close each branch. *)
require import AllCore Distr.

module M = {
  var a : int
  proc f() : int = { return M.a; }
  proc g() : int = { return M.a; }
}.

lemma case_binary : equiv[ M.f ~ M.g : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl case (M.a{1} = 0).
- dcoupl skip. smt().
- dcoupl skip. smt().
qed.

(* Nested case: split twice. *)
lemma case_nested : equiv[ M.f ~ M.g : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl case (M.a{1} = 0).
- dcoupl case (M.a{2} = 0).
  + dcoupl skip. smt().
  + dcoupl skip. smt().
- dcoupl skip. smt().
qed.
