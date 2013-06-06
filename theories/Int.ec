require import Logic.

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

theory Extrema.
  op min(a:int, b:int) = if (a < b) then a else b.

  lemma min_is_lb: forall a b,
    min a b <= a /\
    min a b <= b.

  lemma min_is_glb: forall x a b,
    x <= a => x <= b =>
    x <= min a b.

  lemma min_is_extremum: forall a b,
    min a b = a \/ min a b = b.

(* This is much more satisfying: it defines the notion,
   and proves that it exists and is unique by giving it a
   functional definition. Still, the above definition
   is---probably---more usable.
   Note that the following could be used for iterated versions,
   for example on sets, with a proof that folding the binary min
   over the set fulfills the axioms. *)
(*op min: int -> int -> int.
  axiom min_is_lb: forall a b, min a b <= a /\ min a b <= b.
  axiom min_is_glb: forall x a b, x <= a => x <= b => x <= min a b.
  lemma min_is_extremum: forall a b, min a b = a \/ min a b = b.

  lemma min_def: forall a b,
    min a b = if (a < b) then a else b. *)

  op max(a:int, b:int) = if (a < b) then b else a.

  lemma max_is_ub: forall a b,
    a <= max a b /\
    b <= max a b.

  lemma max_is_lub: forall x a b,
    a <= x => b <= x =>
    max a b <= x.

  lemma max_is_extremum: forall a b,
    max a b = a \/ max a b = b.
end Extrema.
export Extrema.

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

  lemma strongInduction:
    forall (p:int -> bool),
      (forall j, 0 <= j => (forall k, k >= 0 => k < j => p k) => p j) =>
        (forall i, 0 <= i => p i)
    proof.
      intros p hyp i iVal.
      cut temp : (forall k, k > 0 => k <= i => p k);[|trivial].
      apply (Induction.induction (lambda i, forall k, k > 0 => k <= i => p k) _ _ i _);trivial.
  save.
end Induction.

