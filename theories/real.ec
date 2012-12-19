import why3 "real" "Real"
  op "prefix -" as "opp".
  
theory Rdot.
  import why3 "real" "RealInfix"
    op "prefix -." as "opp".
end Rdot.

theory Abs.

  import why3 "real" "Abs".
     (* FIXME NOTATION FOR ABS *)
  (* unset triangular_inequality *)

end Abs.
(* Ca c'est chiant de devoir faire des import et des exports *)
import Abs.
export Abs.

theory Triangle.

  lemma triangular_inequality : forall (x:_,y:_,z:_),
     abs(x-y) <= abs(x-z) + abs(y-z).

end Triangle.

theory FromInt.

   import why3 "real" "FromInt".

end FromInt.
import FromInt.
export FromInt.

theory PowerInt.
  import why3 "real" "PowerInt"
     op "power" as "^".
     
end PowerInt.
import PowerInt.
export PowerInt.



