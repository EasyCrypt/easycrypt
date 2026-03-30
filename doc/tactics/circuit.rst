
========================================================================
Tactic: `circuit`
========================================================================

The ``circuit`` tactic can be used to resolve a multitude of goals where 
the semantics in question are over finite types.

There are currently two variants of this tactic:

- `circuit`, which attempts to automatically solve/prove the goal

- `circuit simplify`, which performs a simplification over the goal structure
  augmented by equivalence checks whenever an equality between two finite types
  with bindings is encountered.

.. contents::
   :local:

..
  ------------------------------------------------------------------------
  Variant: ``circuit`` (FOL)
  ------------------------------------------------------------------------
  .. ecproof::
     :title: First-order logic example

     require import AllCore List QFABV.

     type W8.

     op to_bits : W8 -> bool list.
     op from_bits : bool list -> W8.
     op of_int : int -> W8.
     op to_uint : W8 -> int.
     op to_sint : W8 -> int.
     
     bind bitstring
       to_bits 
       from_bits 
       to_uint 
       to_sint
       of_int 
       W8
       8.

     realize gt0_size by admit.
     realize tolistP by admit.
     realize oflistP by admit.
     realize touintP by admit.
     realize tosintP by admit.
     realize ofintP by admit.
     realize size_tolist by admit.

     op (+^) : W8 -> W8 -> W8.
     bind op W8 (+^) "xor".
     realize bvxorP by admit.

     lemma L (w1 w2 : W8) : w1 +^ w2 = w2 +^ w1.
     proof.
       proc. (*$*) circuit solve.
     abort.

  As we can see, the tactic can, through the generation of the appropriate 
  circuit representing validity of the proposition for a given value and 
  the equation of this function with the constant function equal to true, 
  establish the truth of the lemma.
  This is, in a sense, a reverse use of function extensionality, to convert 
  statements about functions to statements about universal quantification.


------------------------------------------------------------------------
Variant: ``circuit`` (HL)
------------------------------------------------------------------------

.. ecproof::
   :title: Hoare logic example

   require import AllCore List QFABV.

   type W8.

   op to_bits : W8 -> bool list.
   op from_bits : bool list -> W8.
   op of_int : int -> W8.
   op to_uint : W8 -> int.
   op to_sint : W8 -> int.
   
   bind bitstring
     to_bits 
     from_bits 
     to_uint 
     to_sint
     of_int 
     W8
     8.

   realize gt0_size by admit.
   realize tolistP by admit.
   realize oflistP by admit.
   realize touintP by admit.
   realize tosintP by admit.
   realize ofintP by admit.
   realize size_tolist by admit.

   op (+^) : W8 -> W8 -> W8.
   bind op W8 (+^) "xor".
   realize bvxorP by admit.

   module M = {
     proc f(w : W8) = {
       return w +^ w;
     }
   }.

   lemma L (w_ : W8) : hoare[M.f : w_ = w ==> res = of_int 0].
   proof.
     proc. (*$*) circuit.
   abort.


As we can see from the output, the execution of the tactic has several components:

- The translation of the precondition to a circuit, using any explicit equations 
  that define values of program variables at the start of execution in the further
  construction of circuits henceforth.

- The translation of the program to a (collection of) circuits. This is done instruction-wise
  by keeping and updating a mapping from program variables to circuits determining how their 
  value is obtained from the value of some initial "input" variables. In the case of a program 
  these are either logical variables constraining initial values of program variables or the 
  program variables themselves, interpreted as symbols which are then universally quantified.

- The translation of the postcondition into a circuit outputting a boolean, representing whether
  the postcondition holds for given values of the input variables. The knowledge of how the 
  inputs relate to the outputs through the program and the knowledge of any initial relations 
  or known facts about these variables coming from the precondition or proof context is also 
  incorporated into this circuit. The goal of the tactic is then to prove that this circuit 
  is identically true for all values of the input, which is equivalent to the given hoare triple
  being valid/true under the current proof context.

In the case where the goal is an equality, some extra optimization are effected. 
This corresponds to a heuristic inferrence procedure which tries to find structurally identical 
conditions in order to avoid having to check the same condition more than once and also reduce 
the number of inputs which are considered for each condition check, in order to reduce checking time.


------------------------------------------------------------------------
Variant: ``circuit`` (rHL)
------------------------------------------------------------------------

.. ecproof::
   :title: Program equivalence example

   require import AllCore List QFABV.

   type W8.

   op to_bits : W8 -> bool list.
   op from_bits : bool list -> W8.
   op of_int : int -> W8.
   op to_uint : W8 -> int.
   op to_sint : W8 -> int.
   
   bind bitstring
     to_bits 
     from_bits 
     to_uint 
     to_sint
     of_int 
     W8
     8.

   realize gt0_size by admit.
   realize tolistP by admit.
   realize oflistP by admit.
   realize touintP by admit.
   realize tosintP by admit.
   realize ofintP by admit.
   realize size_tolist by admit.

   op (+^) : W8 -> W8 -> W8.
   bind op W8 (+^) "xor".
   realize bvxorP by admit.

   module M = {
     proc f1(w1 w2 : W8) = {
       var a : W8;
       a <- w1 +^ w2;
       return a;
     }

     proc f2(w1 w2 : W8) = {
       var a : W8;
       a <- w2 +^ w1;
       return a;
     }
   }.

   lemma L : equiv[M.f1 ~ M.f2 : ={arg} ==> ={res}].
   proof.
     proc. (*$*) circuit.
   abort.


As we can see in this example, the tactic is also able to automatically prove 
equivalence of these two programs. The way this is done is similar to the way
that single procedures are handled, but now we consider two sets of transformations
from input to outputs variables, one for each program. We then use this knowledge 
to convert the postcondition into the appropriate circuit and use the same procedure 
to attempt to automatically discharge it.
