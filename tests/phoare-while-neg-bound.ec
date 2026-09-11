(* pHL `while` with an invariant only, upper bound (upstream #1102): the
   conditions on the bound (`inv /\ !e /\ post => bd = 1%r`, `0%r <= bd`)
   must be goals quantified over all memories, not part of the
   post-condition of the hoare judgment on the statements preceding the
   loop, which a diverging prefix or a never-established invariant
   discharges vacuously. Here `0%r <= -1%r` must remain, unprovable. *)
require import AllCore Real.

module M = { proc p() = { while (true) {} } }.

lemma bad : phoare[M.p : true ==> false] <= (-1%r).
proof.
proc.
while (true).
+ auto.
+ done.
(* remaining goal: forall &hr, true \/ true => 0%r <= -1%r *)
move=> &hr _.
fail (by smt()).
abort.

(* Invariant `false`, "established" by a diverging prefix: only the
   non-negativity of the bound on the pre-condition rejects it. *)
module N = { proc p() = { while (true) {} while (true) {} } }.

lemma bad' : phoare[N.p : true ==> false] <= (-1%r).
proof.
proc.
while false.
+ auto.
+ while true.
  + done.
  done.
(* remaining goal: forall &hr, true \/ false => 0%r <= -1%r *)
move=> &hr _.
fail (by smt()).
abort.
