(* -------------------------------------------------------------------- *)
require import AllCore List Ring Int SubRing.

(* -------------------------------------------------------------------- *)
abstract theory ComRingModule.
  type scalar, t.

  clone import ComRing as Scalar with type t <= scalar.
  clone import ZModule with type t <- t.

  op ( ** ) : scalar -> t -> t.

  axiom scaleDl (x y : scalar) (a : t) : (x + y) ** a = x ** a + y ** a.
  axiom scaleDr (x : scalar) (a b : t) : x ** (a + b) = x ** a + x ** b.
  axiom scaleM (x y : scalar) (a : t) : (x * y) ** a = x ** (y ** a).
  axiom scale1r (a : t) : oner ** a = a.
end ComRingModule.

(*
abstract theory IDomainModule.

  clone import IDomain as ID.

  clone include ComRingModule with
    theory CR <- ID.

end IDomainModule.


abstract theory VectorSpace.

  clone import Field as F.

  clone include IDomainModule with
    theory ID <- F.

end VectorSpace.
*)


(* -------------------------------------------------------------------- *)
abstract theory SubComRingModule.
  type t, st.

  clone import ComRing as CR with type t <= t.

  clone import SubComRing
    with type t <= t, type st <= st, theory CR <- CR.

  op ( ** ) (x : st) (a : t) : t =
    Sub.val x * a.

  clone ComRingModule with
    type scalar    <- st,
    type t         <- t,
    theory Scalar  <- SubComRing.SCR,
    theory ZModule <- CR,
    op     ( ** )  <- ( ** )

    proof *.

  realize scaleDl. admit. qed.
  realize scaleDr. admit. qed.
  realize scaleM . admit. qed.
  realize scale1r. admit. qed.
end SubComRingModule.
