require import AllCore.

notation #pair (a : int) (b : int) "[" a ", " b "] " = (a, b).

lemma same_file : #pair [1, 2] = (1, 2).
proof. by trivial. qed.
