(* -------------------------------------------------------------------- *)
type t.

op (+): t -> t -> t.

axiom A x y : x + y = y + x.

op f (x y : t) = x + y.

lemma L x y : f x y = y + x.
proof. by apply A. qed.
