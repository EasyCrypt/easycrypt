require int.

import why3 "real" "Real"
  op "prefix -" as "__opp".
  
theory Rdot.
  (* Fixme rebing to the normal  one *)
  import why3 "real" "RealInfix"
    op "prefix -." as "__opp".
end Rdot.

theory Abs.

  import why3 "real" "Abs".
     (* FIXME NOTATION FOR ABS *)
  (* unset triangular_inequality *)

end Abs.
export Abs.

theory Triangle.

  lemma triangular_inequality : forall (x:_,y:_,z:_),
     abs(x-y) <= abs(x-z) + abs(y-z).

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



