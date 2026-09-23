(* pHL `while I v` (strict variant), upstream #1103: for `<=` and `=`, the
   rule must require the invariant (with the termination and exit
   conditions) to hold on every terminating run of the statements preceding
   the loop, `hoare[s : P ==> I /\ ...]`. With `I = false` that goal cannot
   be proved; `>=` needs no such goal; a bound `1%r` needs none either. *)
require import AllCore Real.

op b : bool.

module M = { proc p() = { while (b) {} } }.

lemma bad : phoare[M.p : true ==> true] = 0%r.
proof.
proc.
fail (by while false 0).
abort.

lemma bad' : phoare[M.p : true ==> true] <= 0%r.
proof.
proc.
fail (by while false 0; auto).
abort.

lemma ok : phoare[M.p : true ==> true] >= 0%r.
proof.
proc.
by while false 0.
qed.

module N = { proc q() = { var i : int; i <- 0; while (i < 3) { i <- i + 1; } } }.

lemma ok' : phoare[N.q : true ==> true] = 1%r.
proof.
proc.
while (true) (3 - i).
+ by auto=> /#.
by auto=> /#.
qed.
