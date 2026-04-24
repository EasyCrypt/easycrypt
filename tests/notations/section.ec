require import AllCore.

(* Notations inside a section, including a local one. *)
section.

  notation #gpair (a : int) (b : int) "[" a ", " b "] " = (a, b).

  local notation #lpair (a : int) (b : int) "[" a ", " b "] " = (a, b).

  lemma t_g : #gpair [1, 2] = (1, 2).
  proof. by trivial. qed.

  lemma t_l : #lpair [1, 2] = (1, 2).
  proof. by trivial. qed.

end section.

(* After the section closes, the global notation survives. *)
lemma after : #gpair [3, 4] = (3, 4).
proof. by trivial. qed.
