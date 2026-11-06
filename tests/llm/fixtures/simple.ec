(* Simple conjunction: LOAD stops on line 5 (the `proof.`), leaving one
   open goal `1 = 1 /\ 2 = 2`. *)
require import AllCore.

lemma simple_and : 1 = 1 /\ 2 = 2.
proof.
split.
trivial.
trivial.
qed.
