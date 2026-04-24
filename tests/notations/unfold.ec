require import AllCore List.

(* Unfolding a notation via `rewrite` — since notations are real operators   *)
(* of kind `OB_nott`, the usual delta-rewrite machinery should unfold them. *)

notation #pair (a : int) (b : int) "[" a ", " b "] " = (a, b).

lemma pair_fst (x y : int) : fst (#pair [x, y]) = x.
proof. by trivial. qed.

(* Explicit delta unfold via `rewrite /#pair`. *)
lemma explicit_unfold (x y : int) : #pair [x, y] = (x, y).
proof. by rewrite /#pair. qed.

(* Unfold under a binder. *)
notation #bump (a : int) "[" a "] " = a + 1.

lemma unfold_under_binder :
  map (fun x => #bump [x]) [1; 2; 3] = [2; 3; 4].
proof. by trivial. qed.
