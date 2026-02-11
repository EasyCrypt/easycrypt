========================================================================
Tactic: ``proc``
========================================================================

The ``proc`` tactic applies to program-logic goals where the procedure(s)
under consideration are referred to by name rather than content. It is
typically the first tactic applied when reasoning about procedure calls
or top level program logic statements.

There are two variants of the ``proc`` tactic, depending on whether the 
procedure(s) in question are abstract (i.e., declared but not defined)
or concrete (i.e., defined with a body of code).

The abstract variant is a bit different for probabilistic relational 
Hoare logic compared to the other program logics, so we describe it
separately. When one of the two procedures is abstract and the other is
concrete the ``proc*`` tactic can be used instead.

.. contents::
   :local:

------------------------------------------------------------------------
Variant: Concrete procedure(s)
------------------------------------------------------------------------

.. admonition:: Syntax

  ``proc``

The ``proc`` tactic, when applied to concrete procedures, unfolds the 
procedure definition(s) at hand, replacing the procedure call(s)
with the body(ies) of the corresponding procedure(s). The proof goal is
then updated accordingly.

.. ecproof::
   :title: Hoare logic example

   require import AllCore.

   module M = {
     proc f(x : int) = {
       x <- x + 1;
       x <- x * 2;
       return x;
     }
   }.

   pred p : int.
   pred q : int.

   lemma L : hoare[M.f : p x ==> q res].
   proof.
     (*$*) proc.
   abort.

.. ecproof::
   :title: Probabilistic relational Hoare logic example

   require import AllCore.

   module M1 = {
     proc f(x : int) = {
       x <- x + 1;
       x <- x * 2;
       return x;
     }
   }.

   module M2 = {
     proc f(x : int) = {
       x <- x * 10;
       x <- x - 3;
       return x;
     }
   }.

   pred p : int & int.
   pred q : int & int.

   lemma L : equiv[M1.f ~ M2.f : p x{1} x{2} ==> q res{1} res{2}].
   proof.
     (*$*) proc.
   abort.

------------------------------------------------------------------------
Variant: Abstract procedure (non-relational)
------------------------------------------------------------------------

.. admonition:: Syntax

  ``proc {formulaI}``

Here, ``{formulaI}`` is an invariant that should be preserved by the 
procedure. The invariant can refer to global variables not being modified 
by the procedure. To ensure that variables of interest cannot be modified,
it may be necessary to add restrictions to the module type of the abstract procedure, specifying which globals are not accessed.

The tactic, when applied to abstract procedures, generates a proof
obligation that the invariant holds initially (i.e., it is implied by the 
precondition) and another that the invariant is sufficient to ensure the 
postcondition. For every module argument to the abstract procedure, an 
additional proof obligation is generated to ensure that every procedure in 
the module argument preserves the invariant.

The probabilistic Hoare logic variant only works when the invariant is 
guaranteed to hold with probability 1. Therefore it requires the initial 
bound to be 1 and generates an additional proof obligation requiring that 
losslessness of procedures of the module arguments implies losslessness 
of the procedure under consideration.

.. ecproof::
   :title: Hoare logic example with abstract procedure

   require import AllCore.

   module type OT = {
     proc g1(): int
     proc g2(x: int): unit
   }.

   module type MT (O: OT) = {
     proc f(x : int): int
   }.

   module O = {
     var y: int
     proc g1() = {
       y <- y+1;
       return y;
     }

     proc g2(x: int) = {
     }
   }.

   pred p : int.
   pred q : int.
   pred inv : int.

   lemma L (M <: MT {-O}): hoare[M(O).f : p x ==> q res].
   proof.
     (*$*) proc (inv O.y).
     - admit. (* Invariant holds initially *)
     - admit. (* Invariant implies postcondition *)
     - admit. (* Procedure g1 preserves invariant *)
     (* Procedure g2 preserves invariant *)
   abort.

.. ecproof::
   :title: Probabilistic Hoare logic example with abstract procedure

   require import AllCore.

   module type OT = {
     proc g1(): int
     proc g2(x: int): unit
   }.

   module type MT (O: OT) = {
     proc f(x : int): int
   }.

   module O = {
     var y: int
     proc g1() = {
       y <- y+1;
       return y;
     }

     proc g2(x: int) = {
     }
   }.


   pred p : int.
   pred q : int.
   pred inv : int.

   lemma L (M <: MT {-O}): phoare[M(O).f : p x ==> q res] = 1%r.
   proof.
     (*$*) proc (inv O.y).
     - admit. (* Invariant holds initially *)
     - admit. (* Invariant implies postcondition *)
     - admit. (* Losslessness of M(O).f *)
     - admit. (* Procedure g1 preserves invariant *)
     (* Procedure g2 preserves invariant *)
   abort.

.. ecproof::
   :title: Expectation Hoare logic example with abstract procedure

   require import AllCore Xreal.

   module type OT = {
     proc g1(): int
     proc g2(x: int): unit
   }.

   module type MT (O: OT) = {
     proc f(x : int): int
   }.

   module O = {
     var y: int
     proc g1() = {
       y <- y+1;
       return y;
     }

     proc g2(x: int) = {
     }
   }.


   op p : int -> xreal.
   op q : int -> xreal.
   op inv : int -> xreal.

   lemma L (M <: MT {-O}): ehoare[M(O).f : p x ==> q res].
   proof.
     (*$*) proc (inv O.y).
     - admit. (* Invariant holds initially *)
     - admit. (* Invariant implies postcondition *)
     - admit. (* Procedure g1 preserves invariant *)
     (* Procedure g2 preserves invariant *)
   abort.


------------------------------------------------------------------------
Variant: Abstract procedure (relational)
------------------------------------------------------------------------

The relational variant of the ``proc`` tactic for abstract procedures
requires both procedures to be the same, though their module arguments
may differ.

.. admonition:: Syntax

  - ``proc {formulaI}``
  - ``proc {formulaB} {formulaI}``
  - ``proc {formulaB} {formulaI} {formulaJ}``

Here: 

- ``{formulaI}`` is a two-sided invariant that should be preserved by the
  pair of procedures.
- ``{formulaB}`` is an optional formula representing a bad event on the 
  right side after which the invariant need no longer hold.
- ``{formulaJ}`` is an optional formula representing the invariant after
  the bad event has occurred. This is optional even if ``{formulaB}`` is 
  provided; in which case the invariant is taken to be ``true`` after the 
  bad event.

The tactic can be thought of as keeping both procedures in sync using 
``{formulaI}`` until the bad event ``{formulaB}`` occurs on the right 
side, after which they are no longer kept in sync. Instead ``{formulaJ}`` 
is then preserved by the left and right procedures individually, no matter 
the order in which the two sides make progress.

When only ``{formulaI}`` is provided, the tactic works similarly to the 
non-relational variants, generating proof obligations to ensure that
the invariant, equality of the globals of the module containing the 
procedure and equality of arguments holds and that equality of the 
globals, result and the invariant suffices to ensure the postcondition.
For every procedure of every module argument to the abstract procedure 
an additional proof obligation is generated to ensure that the procedure 
pairs of the module arguments on the left and right preserve the invariant 
and yield equal results when called on equal arguments.

.. ecproof::
   :title: Simple Probabilistic Relational Hoare logic example

   require import AllCore.

   module type OT = {
     proc g1(): int
     proc g2(x: int): unit
   }.

   module type MT (O: OT) = {
     proc f(x : int): int
   }.

   module O1 = {
     var y: int
     proc g1() = {
       y <- y+1;
       return y;
     }

     proc g2(x: int) = {
     }
   }.
   module O2 = {
     var y: int
     proc g1() = {
       return y;
     }

     proc g2(x: int) = {
       y <- y-1;
     }
   }.

   pred p : int & int.
   pred q : int & int.
   pred inv : int & int.

   lemma L (M <: MT {-O1, -O2}): equiv[M(O1).f ~ M(O2).f: p x{1} x{2} ==> q res{1} res{2}].
   proof.
     (*$*) proc (inv O1.y{1} O2.y{2}).
     - admit. (* Invariant holds initially *)
     - admit. (* Invariant implies postcondition *)
     - admit. (* Procedure g1 preserves invariant *)
     (* Procedure g2 preserves invariant *)
   abort.

When ``{formulaB}`` and ``{formulaJ}`` are provided, the equality of 
arguments, results, globals and ``{formulaI}`` obligations are modified to 
only hold/need to hold conditional on the bad event not having occurred on 
the right side. When the bad event has occurred, we instead require that 
``{formulaJ}`` holds without any additional equality requirements. Since 
the behavior of the two sides is no longer synchronized after the bad 
event, an obligation is generated to ensure that the procedure is lossless 
when the procedures in its module arguments are lossless, to avoid the 
weights diverging after the bad event.

For every procedure of every module argument to the abstract procedure on 
the left, an additional proof obligation is generated to ensure that the 
when the bad event has happened and ``{formulaJ}`` holds for some right 
memory, then it is guaranteed to still hold for that right memory after 
running the procedure of the argument on the left. Similarly, for every 
procedure of every module argument to the abstract procedure on the right, 
an additional proof obligation is generated to ensure that when the bad 
event has happened and ``{formulaJ}`` holds for some left memory, then the 
bad event on the right and the two-sided invariant ``{formulaJ}`` is 
guaranteed to still hold for the left memory after running the procedure 
of the argument on the right.

If you want the bad event to be on the left side instead, you can swap the 
two programs using the ``sym`` tactic before applying ``proc``.

.. ecproof::
   :title: Probabilistic Relational Hoare logic example with bad event
    
   require import AllCore.
    
   module type OT = {
     proc g(): unit
   }.
    
   module type MT (O: OT) = {
     proc f(x : int): int
   }.
    
   module O1 = {
     var y: int
     proc g() = {
       y <- y+1;
     }
   }. 
   module O2 = {
     var y: int
     proc g() = {
       y <- y-1;
     }
   }.
    
   pred p : int & int.
   pred q : int & int.
   pred inv : int & int.
   pred bad : int.
   pred inv2 : int & int.
    
   lemma L (M <: MT {-O1, -O2}): equiv[M(O1).f ~ M(O2).f: p x{1} x{2} ==> q res{1} res{2}].
   proof.
     (*$*) proc (bad O2.y) (inv O1.y{1} O2.y{2}) (inv2 O1.y{1} O2.y{2}).
     - admit. (* Connecting precondition to invariants *)
     - admit. (* Connecting invariants to postcondition *)
     - admit. (* Losslessness of M(O).f *)
     - admit. (* Relating O1.g and O2.g during synchronization *)
     - admit. (* Behaviour of O1.g after bad event *)
     (* Behaviour of O2.g after bad event *)
   abort.