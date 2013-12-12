(* -------------------------------------------------------------------- *)
type t.

op o: t -> t.
op p: t -> t -> bool.

axiom A: forall x y, p x y.

lemma l: forall x, p (o x) x.
proof -strict.
  by intros=> x; generalize (o _)=> y; apply (A y x).
qed.
