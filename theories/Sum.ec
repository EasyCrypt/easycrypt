require import FSet. import Interval.
require import Int.
require import Real.
require import Monoid.

(* temporary workaround *)
op intval : int -> int -> int set = interval.

lemma intval_def : forall i i1 i2,
  mem i (intval i1 i2)  <=> (i1<= i /\ i <= i2) by smt.

lemma intval_card_0 :
  forall i1 (i2 : int), i1 <= i2 =>
  card (intval i1 i2) = i2 - i1 + 1 by smt.

lemma intval_card_1 :
  forall i1 (i2:int), i2 < i1 => card (intval i1 i2) = 0 by smt.

op int_sum : (int -> real) -> int set -> real = Mrplus.sum.

pred is_cnst (f : int -> 'a) = forall i1 i2, f i1 = f i2.

lemma int_sum_const :
  forall (f : int -> real) (s: int set), is_cnst f =>
    int_sum f s = (card s)%r * f 0.
intros f s cst.
rewrite /int_sum (Mrplus.NatMul.sum_const (f 0)) //.
intros x hh.
by apply cst.
qed.