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
     
end PowerInt.
export PowerInt.
print theory Int.
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
