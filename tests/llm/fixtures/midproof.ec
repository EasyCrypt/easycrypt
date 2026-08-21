(* Deliberately truncated: the file ends inside the proof, so a bare
   `LOAD "fixtures/midproof.ec"` lands mid-proof with two open goals.
   Used for the LOAD-continuation and -trace scenarios. *)
require import AllCore.

lemma cont_and : 1 = 1 /\ 2 = 2.
proof.
split.
