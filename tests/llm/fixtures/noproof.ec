(* Three lemmas whose proofs `LOAD -noproof' skips -- each is admitted
   on its statement alone -- and a fourth one the LOAD position lands
   inside, whose script is replayed for real. `first_and' is the one
   the scripts `print' afterwards, to show a skipped lemma is bound and
   usable all the same. *)
require import AllCore.

lemma first_and : 1 = 1 /\ 2 = 2.
proof.
split.
trivial.
trivial.
qed.

lemma second_and : 3 = 3 /\ 4 = 4.
proof.
split.
trivial.
trivial.
qed.

lemma third_and : 5 = 5 /\ 6 = 6.
proof.
split.
trivial.
trivial.
qed.

lemma target_and : (1 = 1 /\ 2 = 2) /\ 3 = 3.
proof.
split.
split.
trivial.
trivial.
trivial.
qed.
