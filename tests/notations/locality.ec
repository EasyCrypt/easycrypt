require import AllCore.

(* Global notation: visible after import. *)
theory T1.
  notation #pairT1 (a : int) (b : int) "[" a ", " b "] " = (a, b).

  lemma inside_T1 : #pairT1 [1, 2] = (1, 2).
  proof. by trivial. qed.
end T1.

import T1.

lemma outside_T1_sees_global : #pairT1 [3, 4] = (3, 4).
proof. by trivial. qed.
