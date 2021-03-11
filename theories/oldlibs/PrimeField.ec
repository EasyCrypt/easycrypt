(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require Int IntDiv.
require import Xint.


  (* prime fields GF(q) for q prime *)
theory F.
  (* the order of field is a prime q *)
  op q: int.
  axiom q_pos:  Int.(<) 0 q.
  (* TODO: Add an axiom asserting primality of q. *)

  (* Type of elements of the field *)
  type t.
  op zero : t. (* zero *)
  op one  : t. (* one *)
  op ( * ): t -> t -> t.  (* multiplication modulo q *)
  op ( + ): t -> t -> t.  (* addition modulo q *)
  op [ - ]: t -> t.       (* the additive inverse *)
  op inv: t -> t.         (* the multiplicative inverse *)

  op (-) : t -> t -> t.   (* subtraction modulo q *)
  op (/) : t -> t -> t.   (* division modulo q for y <> 0 *)
  op (^) : t -> int -> t. (* exponentiation *)

  axiom non_trivial: zero <> one.

  (* Addition/Subtraction *)
  axiom addC (x y:t): x + y = y + x.
  axiom addA (x y z:t) : x + (y + z) = (x + y) + z.
  axiom addf0 (x:t): x + zero = x.
  axiom addfN (x:t): x + -x = zero.
  axiom sub_def (x y:t) : x - y = x + -y.

  (* Multiplication *)
  axiom mulC (x y:t): x * y = y * x.
  axiom mulA (x y z:t): x * (y * z) = (x * y) * z.
  axiom mulf1 (x:t): x * one = x.
  axiom mulfV (x:t): x <> zero => (x * (inv x)) = one.
  axiom mulfDl (x y z:t): x * y + x * z = x * (y + z).
  axiom div_def (x y:t): x / y = x * (inv y).

  axiom mulf_eq0:
    forall (x y : t), x * y = zero <=> x = zero \/ y = zero.

  (* Exponentiation *)
  axiom pow0 (x:t): x ^ 0 = one.
  axiom powS (x:t) (n:int): Int.(<=) 0 n => x ^ (Int.(+) n 1) = x * x ^ n.
  axiom powN (x:t) (n:int): Int.(<=) 0 n => x ^ (Int.([-]) n) = inv (x ^ n).

  (** conversion between int and gf_q *)
  op ofint : int -> t.
  op toint : t -> int.

  axiom ofint0: ofint 0 = zero.
  axiom ofintS (n:int): Int.(<=) 0 n => ofint (Int.(+) n 1) = (ofint n) + one.
  axiom ofintN (n:int): ofint (Int.([-]) n) = -(ofint n).

  import Int.
  axiom toint_bounded (x:t): 0 <= toint x < q.
  axiom oftoint (x:t): ofint (toint x) = x.
  axiom toofint_mod (x:int): toint (ofint x) = IntDiv.(%%) x q.

end F.
export F.

(* Declaring the ring and field structure *)
require AlgTactic.
require Ring.

instance ring with t
  op rzero = F.zero
  op rone  = F.one
  op add   = F.( + )
  op opp   = F.([-])
  op mul   = F.( * )
  op expr  = F.( ^ )
  op sub   = F.(-)
  op ofint = ofint

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof expr0     by smt
  proof exprS     by smt
  proof subrE     by smt
  proof ofint0    by smt
  proof ofint1    by smt
  proof ofintS    by smt
  proof ofintN    by smt.

instance field with t
  op rzero = F.zero
  op rone  = F.one
  op add   = F.( + )
  op opp   = F.([-])
  op mul   = F.( * )
  op expr  = F.( ^ )
  op sub   = F.(-)
  op ofint = ofint
  op inv   = inv
  op div   = F.(/)

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof mulrV     by smt
  proof expr0     by smt
  proof exprS     by smt
  proof exprN     by smt
  proof subrE     by smt
  proof divrE     by smt
  proof ofint0    by smt
  proof ofint1    by smt
  proof ofintS    by smt
  proof ofintN    by smt.

(** Lemmas *)
lemma nosmt subff (x:t): (x - x) = zero
by ringeq.

lemma nosmt add0f (x:t): zero + x = x
by ringeq.

lemma nosmt mulf0 (x:t): x * zero = zero
by ringeq.

lemma nosmt mulNf (x y:t): (-x) * y = - (x * y)
by ringeq.

lemma nosmt mulfN (x y:t): y * (-x)= - (y * x)
by ringeq.

lemma nosmt oppK (x:t): -(-x) = x
by ringeq.

lemma nosmt mulfNl (x y z:t): x * y - x * z = x * (y - z)
by ringeq.

lemma nosmt mulN1f (x:t): (-one) * x = -x
by ringeq.

lemma nosmt oppfD (x y:t): (-x) + (-y) = -(x + y)
by ringeq.

import Int.
lemma nosmt toint_pos (x:t): 0 <= toint x
by [].

lemma nosmt toint_lt (x:t): toint x < q
by [].

lemma nosmt toint_le (x:t): toint x <= q - 1
by [].

lemma nosmt toofint (x:int): 0 <= x => x < q => toint (ofint x) = x.
proof.
  move=> Hp Hlt;rewrite toofint_mod IntDiv.modz_small /#.
qed.

lemma nosmt ofint1_: ofint 1 = F.one
by [].

theory FDistr.

  require import Distr.
  require import Real.
  (* distrinution *)
  op dt: t distr.
  op cdt : {int | 0 <= cdt } as ge0_cdt.
  schema cost_dt `{P}: cost [P: dt] = N cdt.
  hint simplify cost_dt.

  axiom dt_fu: is_full dt.

  axiom dt1E: forall (s:t), mu1 dt s = (1%r/q%r)%Real.

  axiom dt_ll: is_lossless dt.

  lemma dt_funi: is_funiform dt.
  proof. by move=> ??;rewrite !dt1E. qed.

  hint exact random : dt_fu dt_ll dt_funi.


end FDistr.

(* ------------------------------------------------------------------------- *)
op cfeq  : int.
op cfadd : int.
op cfsub : int.
op cfmul : int.
op cfdiv : int.

axiom ge0_cf : 0 <= cfeq /\ 0 <= cfadd /\ 0 <= cfsub /\ 0 <= cfmul /\ 0 <= cfdiv /\ 0 <= FDistr.cdt.

schema cost_F0 `{P} : cost[P:F.zero] = '0.
schema cost_feq `{P} {x y : t} : cost [P: x = y] = cost[P:x] + cost[P:y] + N cfeq.
schema cost_fadd `{P} {x1 x2:t} : cost[P:x1 + x2] = cost[P:x1] + cost[P:x2] + N cfadd.
schema cost_fsub `{P} {x y: t} : cost [P:x - y] = cost[P:x] + cost[P:y] + N cfsub.
schema cost_fmul `{P} {x1 x2:t} : cost[P:x1 * x2] = cost[P:x1] + cost[P:x2] + N cfmul.
schema cost_fdiv `{P} {x y: t} : cost [P:x / y] = cost[P:x] + cost[P:y] + N cfdiv.

hint simplify cost_F0, cost_feq, cost_fadd, cost_fsub, cost_fmul, cost_fdiv.
