require import AllCore Xreal.

module M = {
  proc f() : int = {
    var x;
    x <- 1;
    return x;
  }
}.

(* [true]: trivial postcondition, procedure and statement forms. *)
lemma hoareF_true : hoare [M.f : true ==> true].
proof. by auto. qed.

lemma hoareS_true : hoare [M.f : true ==> true].
proof. by proc; auto. qed.

(* [zero]: null expectation, procedure and statement forms. *)
lemma ehoareF_zero : ehoare [M.f : (1%xr) ==> (0%xr)].
proof. by auto. qed.

lemma ehoareS_zero : ehoare [M.f : (1%xr) ==> (0%xr)].
proof. by proc; auto. qed.

(* [exfalso]: false precondition, in every logic and both forms. *)
lemma hoareF_exfalso : hoare [M.f : false ==> res = 2].
proof. by exfalso. qed.

lemma hoareS_exfalso : hoare [M.f : false ==> res = 2].
proof. by proc; exfalso. qed.

lemma bdhoareF_exfalso : phoare [M.f : false ==> res = 2] = 1%r.
proof. by exfalso. qed.

lemma bdhoareS_exfalso : phoare [M.f : false ==> res = 2] = 1%r.
proof. by proc; exfalso. qed.

lemma equivF_exfalso : equiv [M.f ~ M.f : false ==> res{1} <> res{2}].
proof. by exfalso. qed.

lemma equivS_exfalso : equiv [M.f ~ M.f : false ==> res{1} <> res{2}].
proof. by proc; exfalso. qed.
