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

  lemma triangular_inequality x y z:
     `| x-y | <= `| x-z |  + `| y-z |
  by [].

end Triangle.

theory FromInt.
  require import Int.
  import why3 "real" "FromInt".
  lemma from_intM: forall (a b:int),
    (from_int a < from_int b) <=> (a < b)%Int
  by [].
end FromInt.
export FromInt.

theory PowerInt.
  import why3 "real" "PowerInt"
     op "power" as "^".
  axiom pow_inv_pos :
    forall (x : real) (n : int), Int.(<=) 0 n => x ^ (Int.([-]) n) = inv (x ^ n).
   
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

lemma div_def: forall (x:real),
  x / x = x * (from_int 1 / x)
by [].

lemma mul_div: forall (x:real),
  x <> from_int 0 => x / x = from_int 1
by [].

lemma mulrM: forall (x y z:real),
  from_int 0 < z =>
  x < y =>
  x * z < y * z
by [].


op exp : real -> real.
(* TODO : add axioms*)

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
