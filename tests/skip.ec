require import AllCore Xreal.

module M = {
  proc f() : int = {
    var x;
    x <- 1;
    return x;
  }
}.

lemma hoare_skip : hoare [M.f : true ==> res = 1].
proof. proc; wp; skip => //. qed.

lemma ehoare_skip : ehoare [M.f : (1%xr) ==> (1%xr)].
proof. proc; wp; skip => //. qed.

lemma phoare_skip_eq : phoare [M.f : true ==> res = 1] = 1%r.
proof. proc; wp; skip => //. qed.

(* A bound other than 1: the side condition is left to the user. *)
lemma phoare_skip_ge : phoare [M.f : true ==> res = 1] >= (1%r/2%r).
proof. proc; wp; skip => //; smt(). qed.

lemma equiv_skip : equiv [M.f ~ M.f : true ==> ={res}].
proof. proc; wp; skip => //. qed.

lemma errors : equiv [M.f ~ M.f : true ==> ={res}].
proof.
proc.
fail skip.
abort.

lemma errors_le : phoare [M.f : true ==> res = 1] <= 1%r.
proof.
proc.
fail skip.
abort.
