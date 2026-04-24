require import AllCore.

notation #pair ['a 'b] (a : 'a) (b : 'b) "[" a ", " b "] " = (a, b).

(* Tuple projection after a notation call. *)
lemma proj_1 (x y : int) : #pair [x, y].`1 = x.
proof. by trivial. qed.

lemma proj_2 (x y : int) : #pair [x, y].`2 = y.
proof. by trivial. qed.

(* Projection inside a larger expression. *)
lemma compose (x : int) :
  #pair [x, x + 1].`1 + #pair [x, x + 1].`2 = 2 * x + 1.
proof. by smt(). qed.
