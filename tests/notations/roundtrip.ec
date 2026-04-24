require import AllCore List.

(* Form-slot only *)
notation #pair (a : int) (b : int) "[" a ", " b "] " = (a, b).

(* Binder slot with form-slot dependent on it *)
notation #mapI #< i : int > (n : int) (f : i ==> int)
  "[" i " : " n " : " f "] " =
  map f (iota_ 0 n).

lemma L (x y : int) :
  #pair [x, y] = (x, y).
proof. by trivial. qed.

(* The printer must render `(x, y)` back as `#pair [x, y]`. *)
expect "lemma L: forall (x y : int), #pair [x, y]  = #pair [x, y] ."
  by print axiom L.

(* Binder slot round-trip through printer — the RHS is the body expansion *)
lemma M : #mapI [k : 4 : k + 1] = map (fun k => k + 1) (iota_ 0 4).
proof. by trivial. qed.

(* The printer must recover the user-chosen binder name `k` on both sides. *)
expect "lemma M: #mapI [k : 4 : k + 1]  = #mapI [k : 4 : k + 1] ."
  by print axiom M.
