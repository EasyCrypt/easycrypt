(* -------------------------------------------------------------------- *)
type t.

op o: t -> t.
op p: t -> t -> bool.

axiom A: forall x y, p x y.

lemma l: forall x, p (o x) x.
proof. by move=> x; move: (o _)=> y; apply (A y x). qed.

(* -------------------------------------------------------------------- *)
module type I = {}.

(* -------------------------------------------------------------------- *)
lemma L1 (A<:I) &m: exists x, x by exists true.

lemma L2 (A<:I) &m: true.
proof. by elim (L1 A &m). qed.
