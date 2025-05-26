(* -------------------------------------------------------------------- *)
require import AllCore.

lemma test : forall a b c d e f,
    a && b /\ c && d  =>
    e /\ f =>
    a && b /\ c && d /\ e /\ f.
proof.
move=> *.
split 3; assumption.
qed.
