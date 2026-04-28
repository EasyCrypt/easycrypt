require import AllCore.

(* Abstract theory where the notation body references an abstract op. *)
abstract theory Src.
  type t.
  op combine : t -> t -> t.

  notation #c (a : t) (b : t) "[" a ", " b "] " = combine a b.

  lemma combine_self (x : t) : #c [x, x] = combine x x.
  proof. by trivial. qed.
end Src.

(* Clone with concrete op substitution: combine <- Int.(+). *)
clone Src as SumT with
  type t     <- int,
  op combine <- Int.(+).

import SumT.

(* After substitution, #c should expand to `+`. *)
lemma sum_c (a b : int) : #c [a, b] = a + b.
proof. by trivial. qed.

lemma sum_commute (x y : int) : #c [x, y] = x + y.
proof. by trivial. qed.
