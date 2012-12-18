import why3 "int" "Int" 
  (* Il y a un bug dans ecScope il refuse d'avoir deux operateurs avec des 
     types different et la meme syntaxe *)
  op "prefix -" as "opp".


theory Abs.

  import why3 "int" "Abs".
     (* FIXME NOTATION FOR ABS *)
end Abs.
(* Ca c'est chiant de devoir faire des import et des exports *)
import Abs.
export Abs.

theory Triangle.
  lemma triangle_inequality : forall (x:int,y:_,z:_),

     abs(x-y) <= abs(x-z) + abs(y-z).

end Triangle.

theory EuclDiv.

  import why3 "int" "EuclideanDivision"
    op "div" as "/";
    op "mod" as "%".

end EuclDiv.
import Abs.
export EuclDiv.

(* Not sure we should use this one *)
theory Power.
  import why3 "int" "Power"
    op "power" as "^".
end Power.
import Power.
export Power.

(* lemma test : forall (x:int), 0 <= x => 1 <= 2^x. *)



