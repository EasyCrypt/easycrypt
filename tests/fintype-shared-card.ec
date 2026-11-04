require import AllCore IntDiv Group.

type g1, g2.

op p : int.

axiom prime_p : prime p.

clone CyclicGroup as G1 with
  type group <= g1,
  op order <= p.

clone G1.PowZMod as ZP with
  lemma prime_order <- prime_p.

clone CyclicGroup as G2 with
  type group <= g2,
  op order <= p,
  theory PowZMod.ZModE <= ZP.ZModE.

lemma order_eq : G1.order = G2.order.
proof. by []. qed.
