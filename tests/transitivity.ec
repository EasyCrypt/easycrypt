require import AllCore.

module M = {
  proc f(a : int) : int = {
    var x, y;
    x <- a;
    y <- x + 1;
    return y;
  }

  proc g(a : int) : int = {
    var z;
    z <- a + 1;
    return z;
  }

  proc h(a : int) : int = {
    var w;
    w <- a;
    w <- w + 1;
    return w;
  }
}.

(* -------------------------------------------------------------------- *)
(* Statement form, the intermediate program replacing the left one.      *)
lemma trans_stmt_left : equiv [M.f ~ M.g : ={a} ==> ={res}].
proof.
proc.
transitivity {1} { y <- a + 1; } (={a} ==> ={y}) (={a} ==> y{1} = z{2}).
- by move=> &1 &2 h; exists a{1}; rewrite h.
- by move=> &1 &m &2 -> ->.
- by wp; skip.
- by wp; skip.
qed.

(* Statement form, the intermediate program replacing the right one.     *)
lemma trans_stmt_right : equiv [M.f ~ M.g : ={a} ==> ={res}].
proof.
proc.
transitivity {2} { z <- a; z <- z + 1; } (={a} ==> y{1} = z{2}) (={a} ==> ={z}).
- by move=> &1 &2 h; exists a{2}; rewrite h.
- by move=> &1 &m &2 -> ->.
- by wp; skip.
- by wp; skip.
qed.

(* -------------------------------------------------------------------- *)
(* Procedure form.                                                       *)
lemma trans_fun : equiv [M.f ~ M.g : ={a} ==> ={res}].
proof.
transitivity M.h (={a} ==> ={res}) (={a} ==> ={res}).
- by move=> &1 &2 h; exists a{1}; rewrite h.
- by move=> &1 &m &2 -> ->.
- by proc; wp; skip.
- by proc; wp; skip.
qed.

(* -------------------------------------------------------------------- *)
(* [transitivity*]: the composition side conditions are closed.          *)
lemma trans_eq_left : equiv [M.f ~ M.g : ={a} ==> ={res}].
proof.
proc.
transitivity* {1} { y <- a + 1; }.
- by wp; skip.
- by wp; skip.
qed.

lemma trans_eq_right : equiv [M.f ~ M.g : ={a} ==> ={res}].
proof.
proc.
transitivity* {2} { z <- a; z <- z + 1; }.
- by wp; skip.
- by wp; skip.
qed.

(* A one-sided precondition on the replaced side is kept.                *)
lemma trans_eq_sided : equiv [M.f ~ M.g : ={a} /\ 0 <= a{1} ==> ={res}].
proof.
proc.
transitivity* {1} { y <- a + 1; }.
- by wp; skip.
- by wp; skip.
qed.

(* -------------------------------------------------------------------- *)
(* [replace]: the new program reuses the named parts of the current one. *)
lemma repl_left : equiv [M.f ~ M.g : ={a} ==> ={res}].
proof.
proc.
replace {1} { s1; s2 } by { s1; s2; x <- 0; } (={a} ==> ={y}) (={a} ==> y{1} = z{2}).
- by move=> &1 &2 h; exists a{1}; rewrite h.
- by move=> &1 &m &2 -> ->.
- by wp; skip.
- by wp; skip.
qed.

lemma repl_eq_left : equiv [M.f ~ M.g : ={a} ==> ={res}].
proof.
proc.
replace* {1} { s1; s2 } by { s1; x <- 0; s2; }.
- by wp; skip.
- by wp; skip.
qed.

lemma repl_eq_right : equiv [M.g ~ M.f : ={a} ==> ={res}].
proof.
proc.
replace* {2} { s1; s2 } by { s1; s2; x <- 0; }.
- by wp; skip.
- by wp; skip.
qed.

(* -------------------------------------------------------------------- *)
(* Error paths.                                                          *)
lemma errors_fun : equiv [M.f ~ M.g : ={a} ==> ={res}].
proof.
fail transitivity* M.h.
fail transitivity {1} { y <- a + 1; } (={a} ==> ={y}) (={a} ==> y{1} = z{2}).
fail replace* {1} { s } by { s; }.
abort.

lemma errors_stmt : equiv [M.f ~ M.g : ={a} ==> ={res}].
proof.
proc.
fail transitivity* M.h.
fail transitivity M.h (={a} ==> ={res}) (={a} ==> ={res}).
abort.

lemma errors_other : hoare [M.f : true ==> true].
proof.
fail transitivity* M.h.
fail transitivity M.h (true ==> true) (true ==> true).
fail transitivity {1} { y <- a + 1; } (true ==> true) (true ==> true).
proc.
fail transitivity* {1} { y <- a + 1; }.
fail replace* {1} { s } by { s; }.
abort.
