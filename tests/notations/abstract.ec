require import AllCore.

(* Abstract theory parameterized by `t`, declaring a notation that uses it. *)
abstract theory AbsT.
  type t.

  notation #pairT (a : t) (b : t) "[" a ", " b "] " = (a, b).
end AbsT.

(* Clone with t := int. *)
clone AbsT as IntT with
  type t <- int.

import IntT.

lemma check : #pairT [1, 2] = (1, 2).
proof. by trivial. qed.
