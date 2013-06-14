require Int.

import why3 "real" "Real"
  op "prefix -" as "-!".

theory Abs.

  import why3 "real" "Abs"
    op "abs" as "__abs".
  (* unset triangular_inequality *)

end Abs.
export Abs.

theory Triangle.

  lemma triangular_inequality : forall (x:_,y:_,z:_),
     `| x-y | <= `| x-z |  + `| y-z |
  by [].

end Triangle.

theory FromInt.

   import why3 "real" "FromInt".

end FromInt.
export FromInt.

theory PowerInt.
  import why3 "real" "PowerInt"
     op "power" as "^".
     
end PowerInt.
export PowerInt.

theory Square.
  import why3 "real" "Square"
    op "sqrt" as "sqrt".
end Square.
export Square.

op exp : real -> real.
(* TODO : add axioms*)
