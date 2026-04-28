require import AllCore.

(* Form-slot notation: #cond [c : t | f] expands to if c then t else f. *)
notation #cond (c : bool) (t : int) (f : int) "[" c " : " t " | " f "] " =
  if c then t else f.

lemma t1 : #cond [true : 1 | 2] = 1.
proof. by trivial. qed.

lemma t2 (x y : int) : #cond [x < y : x | y] = if x < y then x else y.
proof. by trivial. qed.

(* Multiple notations in one file; later notation uses earlier-bound ops. *)
notation #max (a : int) (b : int) "[" a ", " b "] " =
  if a < b then b else a.

lemma t3 (x y : int) : #max [x, y] = if x < y then y else x.
proof. by trivial. qed.
