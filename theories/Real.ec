(* --------------------------------------------------------------------
 * Copyright IMDEA Software Institute / INRIA - 2013, 2014
 * -------------------------------------------------------------------- *)

require Int.

import why3 "real" "Real"
  op "prefix -" as "[-]".

theory Abs.

  import why3 "real" "Abs"
    op "abs" as "`|_|".
  (* unset triangular_inequality *)

end Abs.
export Abs.

theory Triangle.

  lemma triangular_inequality (x y z:real):
     `| x-y | <= `| x-z |  + `| y-z |
  by [].

end Triangle.

theory FromInt.
  require import Int.
  import why3 "real" "FromInt".
  lemma from_intM (a b:int):
    (from_int a < from_int b) <=> (a < b)%Int
  by (split; smt).

  lemma from_intMle : forall (a b : int), from_int a <= from_int b <=> a <= b
  by [].

end FromInt.
export FromInt.

theory PowerInt.
  import why3 "real" "PowerInt"
     op "power" as "^".

  axiom pow_inv_pos :
    forall (x : real) (n : int), Int.(<=) 0 n => x ^ (Int.([-]) n) = inv (x ^ n).

  axiom pow_div_den (a b:int):
    Int.(<=) a b =>
    from_int (Int.(^) 2 a) / from_int (Int.(^) 2 b)
    = from_int 1 / from_int (Int.(^) 2 (Int.(-) b a)).
end PowerInt.
export PowerInt.

theory Square.
  import why3 "real" "Square"
    op "sqrt" as "sqrt".
end Square.
export Square.

lemma real_lt_trans: forall (a b c:real), 
 a < b => b <= c => a < c
by [].

lemma div_def (x y:real):
  y <> from_int 0 =>
  x / y = x * (from_int 1 / y)
by [].

lemma mul_div: forall (x:real),
  x <> from_int 0 => x / x = from_int 1
by [].

axiom mulrM: forall (x y z:real),
  from_int 0 < z =>
  x < y =>
  x * z < y * z.
(* by []. *) (* FIXME it should be a lemma *)

lemma nosmt addleM : forall (x1 x2 y1 y2:real),
   x1 <= x2 => y1 <= y2 => x1 + y1 <= x2 + y2 
by [].

lemma nosmt addgeM : forall (x1 x2 y1 y2:real),
   x1 >= x2 => y1 >= y2 => x1 + y1 >= x2 + y2 
by [].

lemma real_abs_sum : forall (a b c:real),
 a = b + c => `|a| <= `|b| + `|c|
by smt.

lemma real_le_trans: forall (a b c:real), 
 a <= b => b <= c => a <= c
by [].

lemma nosmt le_ge : forall (x y:real), (x <= y) <=> (y >= x)
by [].

lemma nosmt le_ge_sym : forall (x y:real), (x <= y) => (y >= x)
by (intros x y;rewrite le_ge).

lemma nosmt eq_le_ge : forall (x y:real), (x = y) <=> (x <= y /\ x >= y)
by [].

lemma nosmt eq_le: forall (x y:real), x = y => x <= y
by [].

theory Exp.

  import why3 "real" "ExpLog"
    op "exp" as "exp".
  axiom exp_zero : exp (from_int 0) = from_int 1.
  axiom exp_monotonous : forall (x y:real) , x<=y => exp x <= exp y.

end Exp.
export Exp.


require import Ring.
require import AlgTactic.

instance ring with real
  op rzero = zero
  op rone  = one
  op add   = ( + )
  op opp   = ([-])
  op mul   = ( * )
  op expr  = PowerInt.( ^ )
  op sub   = (-)
  op ofint = FromInt.from_int

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

instance field with real
  op rzero = zero
  op rone  = one
  op add   = ( + )
  op opp   = ([-])
  op mul   = ( * )
  op expr  = PowerInt.( ^ )
  op sub   = (-)
  op ofint = FromInt.from_int
  op inv   = inv
  op div   = (/)

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
