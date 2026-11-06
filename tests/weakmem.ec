(* The `weakmem` tactic: a hypothesis, a judgement on a statement, is
   weakened by fresh local variables declared in its memory (through the
   weakmem rule of its logic: hoare, ehoare, phoare and equiv, on each
   side and on both sides at once), and added as a premise of the goal;
   and the error paths. Each tactic is a separate sentence, so that the
   goals it leaves can be compared across builds. *)
require import AllCore Xreal.

(* Turns the goal [G] into [G] and [G => G], so that a judgement on a
   statement can be a hypothesis. *)
lemma dup (b : bool) : b => (b => b) => b.
proof. by []. qed.

module M = {
  var g : int

  proc f() : int = {
    var x : int;
    x <- 1;
    return x;
  }

  proc h() : unit = {
    M.g <- 1;
  }
}.

(* -------------------------------------------------------------------- *)
(* hoare: the weakened hypothesis proves the judgement on the memory
   extended by [alias]. *)
lemma L_hoare : hoare [M.f : true ==> res = 1].
proof.
proc.
apply dup; first by auto.
move=> h.
alias 1 y = 0.
weakmem h (y : int).
move=> h'.
seq 1 : true.
- by auto.
exact h'.
qed.

(* several variables, an anonymous one, and a side (ignored) *)
lemma L_hoare_multi : hoare [M.f : true ==> res = 1].
proof.
proc.
apply dup; first by auto.
move=> h.
weakmem h (y : int, _ : bool, z : int * bool).
move=> _.
weakmem {2} h (y : int).
move=> _.
weakmem h ().
move=> _.
exact h.
qed.

(* the errors *)
lemma L_hoare_err : hoare [M.f : true ==> res = 1].
proof.
proc.
apply dup; first by auto.
move=> h.
have t : true by done.
fail weakmem nosuchhyp (y : int).
fail weakmem t (y : int).
fail weakmem h (x : int).
fail weakmem h (y : int, y : bool).
fail weakmem h (y).
fail weakmem h (y : nosuchtype).
exact h.
qed.

(* -------------------------------------------------------------------- *)
(* ehoare *)
lemma L_ehoare : ehoare [M.h : (1%xr) ==> (1%xr)].
proof.
proc.
apply dup; first by auto.
move=> h.
weakmem h (y : int).
move=> h'.
fail weakmem h (y y : int).
exact h.
qed.

(* -------------------------------------------------------------------- *)
(* phoare *)
lemma L_phoare : phoare [M.f : true ==> res = 1] = 1%r.
proof.
proc.
apply dup; first by auto.
move=> h.
weakmem h (y : int, z : bool).
move=> h'.
fail weakmem h (x : int).
exact h.
qed.

(* -------------------------------------------------------------------- *)
(* equiv: each side, and both sides *)
lemma L_equiv : equiv [M.f ~ M.f : true ==> ={res}].
proof.
proc.
apply dup; first by auto.
move=> h.
weakmem {1} h (y : int).
move=> h1.
weakmem {2} h (y z : int).
move=> h2.
weakmem h (y : int).
move=> h3.
alias{1} 1 y = 0.
alias{2} 1 y = 0.
seq 1 1 : true.
- by auto.
exact h3.
qed.

lemma L_equiv_err : equiv [M.f ~ M.f : true ==> ={res}].
proof.
proc.
apply dup; first by auto.
move=> h.
fail weakmem h (x : int).
fail weakmem {1} h (x : int).
fail weakmem {2} h (x : int).
fail weakmem h (y y : int).
exact h.
qed.
