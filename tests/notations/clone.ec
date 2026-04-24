require import AllCore.

(* Theory with a notation. *)
theory Src.
  notation #twice (a : int) "[" a "] " = a + a.

  lemma inside : #twice [3] = 6.
  proof. by trivial. qed.
end Src.

(* Clone brings the notation into the new namespace. *)
clone Src as Dst.
import Dst.

lemma cross_clone : #twice [7] = 14.
proof. by trivial. qed.
