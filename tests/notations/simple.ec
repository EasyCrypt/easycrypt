require import AllCore.

(* Minimal notation: #pair [a, b] expands to (a, b). *)
notation #pair (a : int) (b : int) "[" a ", " b "] " = (a, b).

lemma test1 : #pair [3, 4] = (3, 4).
proof. by trivial. qed.
