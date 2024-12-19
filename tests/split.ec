(* -------------------------------------------------------------------- *)
require import AllCore.

print andWr.

lemma test : forall a b c d e f,
    a && b /\ c && d  =>
    e /\ f =>
    a && b /\ c && d /\ e /\ f.
proof.
move=> *.
split 3.
assumption.
assumption.
qed.
