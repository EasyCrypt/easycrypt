(* -------------------------------------------------------------------- *)
require import AllCore.

print andWr.

lemma test : forall a b c d e f, a && b /\ c && d /\ e /\ f.
proof.
move=> *.

split 5.
split.
admit.



gl = a && b
gr = c /\ d

proja2 gl = b

conja (proja1 gl) (conj (proja2 gl) gr) = a && (b /\ (c /\ d))



admit.



admit.




abort.

