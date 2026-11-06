(* Nested conjunction: `split. split. split.` from the state at line 6
   opens four goals nested as [1.1.1] [1.1.2] [1.2] [2]. *)
require import AllCore.

lemma nested_and : ((1 = 1 /\ 2 = 2) /\ 3 = 3) /\ 4 = 4.
proof.
split.
split.
split.
trivial.
trivial.
trivial.
trivial.
qed.
