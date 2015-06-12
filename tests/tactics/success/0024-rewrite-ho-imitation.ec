(* -------------------------------------------------------------------- *)
type t.

op z     : t.
op ( + ) : t -> t -> t.
op ( * ) : t -> t -> t.
op o     : (t -> t) -> t.

axiom A : forall f c, o (fun x => f x * c) = (o f) * c.

lemma L c : o (fun x => (x + z) * c) = o (fun x => x + z) * c.
proof. by rewrite A. qed.
