import why3 "int" "Int" 
  (* Il y a un bug dans ecScope il refuse d'avoir deux operateurs avec des 
     types different et la meme syntaxe *)
  op "prefix -" as "-!".

theory Abs.

  import why3 "int" "Abs"
    op "abs" as "__abs".

end Abs.
export Abs.

theory Triangle.
  lemma triangle_inequality : forall (x:int,y:_,z:_),
     `| x - y | <= `| x - z | + `| y - z |.

end Triangle.

theory EuclDiv.

  import why3 "int" "EuclideanDivision"
    op "div" as "/";
    op "mod" as "%".

end EuclDiv.
export EuclDiv.

(* Not sure we should use this one *)
theory Power.
  import why3 "int" "Power"
    op "power" as "^".
end Power.
export Power.

(* lemma test : forall (x:int), 0 <= x => 1 <= 2^x. *)

theory Induction.
  axiom induction: forall (p:int -> bool),
    (p 0) =>
    (forall j, 0 < j => p (j - 1) => p j) =>
    (forall i, 0 <= i => p i).
end Induction.

