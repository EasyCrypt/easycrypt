(* pHL `while` with an invariant only, upper bound (upstream #1102): the
   conditions on the bound (`inv /\ !e /\ post => bd = 1%r`, `0%r <= bd`)
   must be goals quantified over all memories, not part of the
   post-condition of the hoare judgment on the statements preceding the
   loop, which a diverging prefix or a never-established invariant
   discharges vacuously. Under #1105 a pHL judgment with a bound that is
   negative in some memory is false, so the non-negativity goal is
   unconditional. Here `0%r <= -1%r` must remain, unprovable. *)
require import AllCore Real.

module M = { proc p() = { while (true) {} } }.

lemma bad : phoare[M.p : true ==> false] <= (-1%r).
proof.
proc.
while (true).
+ auto.
+ done.
(* remaining goal: forall &hr, 0%r <= -1%r *)
move=> &hr.
fail (by smt()).
abort.

(* Invariant `false`, "established" by a diverging prefix: only the
   non-negativity of the bound rejects it. *)
module N = { proc p() = { while (true) {} while (true) {} } }.

lemma bad' : phoare[N.p : true ==> false] <= (-1%r).
proof.
proc.
while false.
+ auto.
+ while true.
  + done.
  done.
(* remaining goal: forall &hr, 0%r <= -1%r *)
move=> &hr.
fail (by smt()).
abort.
