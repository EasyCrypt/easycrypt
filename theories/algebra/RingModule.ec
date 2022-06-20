require import AllCore List Ring Int SubRing.


abstract theory ComRingModule.

  clone import ComRing as CR.

  clone include ZModule.

  op ( ** ) : CR.t -> t -> t.

  axiom compat_addl (x y : CR.t) (a : t) : (x + y) ** a = x ** a + y ** a.
  axiom compat_addr (x : CR.t) (a b : t) : x ** (a + b) = x ** a + x ** b.
  axiom compat_mul (x y : CR.t) (a : t) : (x * y) ** a = x ** (y ** a).
  axiom compat_one (a : t) : CR.oner ** a = a.

end ComRingModule.


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


abstract theory SubComRingModule.

  clone include SubComRing.

  clone include ComRingModule with
    theory CR <- SCR.

  clone import ZModule as ZMod.

  type st.

  op w : ZMod.t.

  (*TODO: issue in FiniteField if this is a pred.*)
  op in_sub : ZMod.t -> bool.

  axiom sub_w : in_sub w.
  axiom sub_add x y : in_sub x => in_sub y => in_sub (x + y).
  axiom sub_opp x : in_sub x => in_sub (-x).

  lemma sub_0 : in_sub zeror.
  proof. by rewrite -(subrr w); apply/sub_add; [apply/sub_w|apply/sub_opp/sub_w]. qed.

  clone Subtype as Sub with
    type T <- ZMod.t,
    type sT <- st,
    pred P <- in_sub.

  op zeror = Sub.insubd zeror.
  op (+) x y = Sub.insubd (Sub.val x + Sub.val y).
  op ([-]) x = Sub.insubd (- Sub.val x).

  clone import ZModule as SZMod with
    type t    <- st,
    op zeror  <- zeror,
    op (+)    <- (+),
    op [-]  <- ([-])
    proof *.

end SubComRingModule.
