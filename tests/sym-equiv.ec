require import AllCore.

module M = {
  proc f(a : int) : int = {
    var x;
    x <- a + 1;
    return x;
  }

  proc g(b : int) : int = {
    var y, z;
    y <- b;
    z <- y;
    return z;
  }
}.

(* Procedure form: the procedures are exchanged, and the memories of the
   pre- and postcondition (including [res]) are swapped. *)
lemma g_f : equiv [M.g ~ M.f : b{1} = a{2} + 1 ==> res{1} = res{2}].
proof. by proc; auto. qed.

lemma f_g : equiv [M.f ~ M.g : a{1} + 1 = b{2} ==> res{2} = res{1}].
proof. by symmetry; conseq g_f. qed.

lemma f_g_exact : equiv [M.f ~ M.g : b{2} = a{1} + 1 ==> res{2} = res{1}].
proof. symmetry; exact g_f. qed.

(* Statement form: the statements, and the types of the memories (here,
   different local variables), are exchanged. *)
lemma f_g_stmt : equiv [M.f ~ M.g : a{1} + 1 = b{2} ==> res{1} = res{2}].
proof.
proc; symmetry.
wp; skip => /> &1 &2.
qed.

lemma f_g_stmt_locals : equiv [M.f ~ M.g : a{1} + 1 = b{2} ==> res{1} = res{2}].
proof.
proc; symmetry.
conseq (: b{1} = a{2} + 1 ==> z{1} = x{2}) => //.
by sp; skip.
qed.

(* Errors: [symmetry] only applies to equiv judgements. *)
lemma hoare_sym : hoare [M.f : a = 1 ==> res = 2].
proof.
fail symmetry.
proc.
fail symmetry.
by auto.
qed.

lemma phoare_sym : phoare [M.f : a = 1 ==> res = 2] = 1%r.
proof.
fail symmetry.
proc.
fail symmetry.
by auto.
qed.
