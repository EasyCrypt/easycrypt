require Int.


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
  axiom toofint_mod (x:int): toint (ofint x) = Int.(%%) x q. 
end F.
export F.

(** Lemmas *)
lemma subff (x:t): (x - x) = zero
by [].

lemma add0f (x:t): zero + x = x
by [].

lemma mulf0 (x:t): x * zero = zero
by [].

lemma mulNf (x y:t): (-x) * y = - (x * y)
by [].

lemma mulfN (x y:t): y * (-x)= - (y * x)
by [].  

lemma nosmt oppK (x:t): -(-x) = x
by [].

lemma mulfNl (x y z:t): x * y - x * z = x * (y - z)
by [].

lemma mulN1f (x:t): (-one) * x = -x
by [].

lemma oppfD (x y:t): (-x) + (-y) = -(x + y)
by [].

import Int.
lemma toint_pos (x:t): 0 <= toint x
by [].

lemma toint_lt (x:t): toint x < q
by [].

lemma toint_le (x:t): toint x <= q - 1
by [].

lemma toofint (x:int): 0 <= x => x < q => toint (ofint x) = x.
proof.
  intros Hp Hlt;rewrite toofint_mod.
  by cut H:= ediv_unique x q 0 x _; smt.
qed.

lemma ofint1_: ofint 1 = F.one 
by [].

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

theory FDistr.

  require import Distr.
  require import Real.
  (* distrinution *)
  op dt: t distr.

  axiom supp_def: forall (s:t),
    in_supp s dt.

  axiom mu_x_def_in: forall (s:t),
    mu_x dt s = (1%r/q%r)%Real.

  axiom lossless: weight dt = 1%r.

end FDistr.

