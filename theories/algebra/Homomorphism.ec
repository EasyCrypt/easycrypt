require import Group.

theory GroupHom.

clone Group as S.
clone Group as T.

type s = S.group.
type t = T.group.

op map : s -> t.
axiom mul (x y : s) : map (S.( * ) x y) = T.( * ) (map x) (map y).

lemma id : map S.e = T.e.
proof.    
  rewrite -(T.mul1c (map S.e)).    
  rewrite -(T.mulVc (map S.e)).
  rewrite -(T.mulcA).
  apply (congr1 (T.( * ) (T.inv (map S.e)))).
  rewrite -mul.
  by rewrite S.mul1c.
qed.

lemma inv (x : s) : map (S.inv x) = T.inv (map x).
proof.
  apply (T.mulcI (map x)).
  rewrite T.mulcV.
  rewrite -mul.
  rewrite S.mulcV.
  by rewrite id.
qed.

require import Int.
require StdOrder.
import StdOrder.IntOrder.

lemma exp (x : s) (k : int) : map (S.( ^ ) x k) = T.( ^ ) (map x) k.
proof.
  wlog: k / (0 <= k).

  move=> ind.

  case (0 <= k).
  by move=> /ind.

  move=> /ltrNge /ltrW.
  rewrite -(oppzK k).
  move=> /oppr_le0.
  pose r := -k.
  move=> /ind ass.
  rewrite S.expN.
  rewrite T.expN.
  rewrite inv.
  by rewrite ass.  

  elim: k.
  rewrite S.exp0.
  rewrite T.exp0.
  by rewrite id.  

  move=> k h ih.
  rewrite T.expS.
  rewrite S.expS.
  rewrite mul.
  apply (T.mulIc (T.inv (map x))).
  rewrite -!T.mulcA.
  rewrite !T.mulcV.
  by rewrite !T.mulc1.
qed.

end GroupHom.
