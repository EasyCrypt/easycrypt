(* conseq: weaken pre and strengthen post. *)
require import AllCore Distr.

module M = {
  var a : int
  proc f() : int = { return M.a; }
  proc g() : int = { return M.a; }
}.

(* Strengthen the pre and weaken the post — both trivial. *)
lemma conseq_trivial :
  equiv[ M.f ~ M.g : ={M.a} ==> ={M.a} ].
proof.
proc. delay.
dcoupl conseq (={M.a}) (={M.a}).
- smt().
- smt().
- dcoupl skip. smt().
qed.

(* Use conseq to introduce an auxiliary invariant. *)
lemma conseq_auxiliary :
  equiv[ M.f ~ M.g : ={M.a} /\ M.a{1} = 0 ==> ={M.a} ].
proof.
proc. delay.
dcoupl conseq (={M.a}) (={M.a}).
- smt().
- smt().
- dcoupl skip. smt().
qed.
