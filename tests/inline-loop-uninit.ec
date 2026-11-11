(* Inlining a call inside a loop body must not let the callee's locals
 * keep their value from one iteration to the next. *)
require import AllCore.

module M = {
  var x : int

  (* reads its local [r] before writing it *)
  proc f() = { var r : int; x <- r; r <- 1; }

  (* never reads a local before writing it *)
  proc g(a : int) = { var r : int; r <- a + 1; x <- r; }

  proc o() : int = {
    var r : int;
    if (x = 0) { r <- 0; }
    return r;
  }

  proc mf() = {
    var i : int;
    i <- 0;
    while (i < 2) { f(); i <- i + 1; }
  }

  proc mif() = {
    var i : int;
    i <- 0;
    while (i < 2) { if (i = 1) { f(); } i <- i + 1; }
  }

  proc mo() = {
    var i, y : int;
    i <- 0;
    while (i < 2) { y <@ o(); i <- i + 1; }
  }

  proc mg() = {
    var i : int;
    i <- 0;
    while (i < 2) { g(i); i <- i + 1; }
  }

  proc seqf() = { f(); f(); }
}.

(* -------------------------------------------------------------------- *)
(* Unsound: the second iteration would see [r = 1] *)
lemma L_f : hoare [M.mf : true ==> M.x = 1].
proof.
proc.
fail inline 2.1.
fail inline M.f.
fail inline *.
abort.

lemma L_if : hoare [M.mif : true ==> true].
proof.
proc.
fail inline 2.1.1.
fail inline *.
abort.

lemma L_o : hoare [M.mo : true ==> true].
proof.
proc.
fail inline *.
abort.

lemma L_f_equiv : equiv [M.mf ~ M.mf : true ==> true].
proof.
proc.
fail inline{1} 2.1.
fail inline{2} M.f.
fail inline *.
abort.

lemma L_f_phoare : phoare [M.mf : true ==> true] = 1%r.
proof.
proc.
fail inline 2.1.
fail inline *.
abort.

(* -------------------------------------------------------------------- *)
(* Fine: the callee does not depend on the initial value of its locals *)
lemma L_g : hoare [M.mg : true ==> M.x = 2].
proof.
proc; inline 2.1.
while (0 <= i <= 2 /\ (1 <= i => M.x = i)).
+ by auto => /> /#.
by auto => /> /#.
qed.

lemma L_g_star : equiv [M.mg ~ M.mg : ={M.x} ==> ={M.x}].
proof. by proc; inline *; sim. qed.

(* Fine: outside of a loop, the fresh copies are unconstrained *)
lemma L_seqf : hoare [M.seqf : true ==> true].
proof. by proc; inline *; auto. qed.

(* Fine: inlining in the body, once the loop rule has been applied *)
lemma L_f_body : hoare [M.mf : true ==> true].
proof.
proc; while true.
+ by inline *; auto.
by auto.
qed.
