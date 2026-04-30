========================================================================
Tactic: `skip`
========================================================================

The ``skip`` tactic applies to program-logic goals where the program(s)
under consideration are empty. In this situation, program execution
performs no computation and produces no state changes.

Applying ``skip`` eliminates the program component of the goal and reduces
the proof obligation to a pure logical goal. Concretely, the remaining
task is to prove that the precondition implies the postcondition.

The ``skip`` tactic does not attempt to solve this logical obligation itself.

.. contents::
   :local:

------------------------------------------------------------------------
Variant: ``skip`` (HL)
------------------------------------------------------------------------

.. ecproof::
   :title: Hoare logic example

   require import AllCore.

   module M = {
     proc f(x : int) = {
       return x;
     }
   }.

   pred p : int.
   pred q : int.

   lemma L : hoare[M.f : p x ==> q res].
   proof.
     proc. (*$*) skip.
   abort.

------------------------------------------------------------------------
Variant: ``skip`` (pRHL)
------------------------------------------------------------------------

In the relational Hoare logic setting, the `skip`` tactic applies only
when both programs are empty, in which case it reduces the relational
judgment to obligations on the preconditions and postconditions alone.

.. ecproof::
   :title: Probabilistic Relational Hoare logic example

   require import AllCore.

   module M = {
     proc f(x : int) = {
       return x;
     }
   }.

   pred p : int & int.
   pred q : int & int.

   lemma L : equiv[M.f ~ M.f : p x{1} x{2} ==> q res{1} res{2}].
   proof.
     proc. (*$*) skip.
   abort.

------------------------------------------------------------------------
Variant: ``skip`` (pHL)
------------------------------------------------------------------------

In the probabilistic Hoare logic setting, applying ``skip`` generates an
additional proof obligation compared to the pure Hoare case. Besides the
logical implication between the precondition and the postcondition, one
must also prove that the probability weight of the empty program, namely
``1%r``, satisfies the bound specified in the judgment.

.. ecproof::
   :title: Probabilistic Hoare logic example

   require import AllCore.

   module M = {
     proc f(x : int) = {
       return x;
     }
   }.

   pred p : int.
   pred q : int.

   lemma L : phoare[M.f : p x ==> q res] >= (1%r / 2%r).
   proof.
     proc. (*$*) skip.
   abort.

------------------------------------------------------------------------
Variant: ``skip`` (eHL)
------------------------------------------------------------------------

In expectation Hoare logic, where the precondition and postcondition are
respectively a pre-expectation and a post-expectation, applying skip generates
the obligation to prove that the post-expectation is bounded above by the
pre-expectation.

.. ecproof::
   :title: Expectation Hoare logic example

   require import AllCore Xreal.
   
   module M = {
     proc f(x : int) = {
       return x;
     }
   }.
   
   op p : int -> xreal.
   op q : int -> xreal.
   
   lemma L : ehoare[M.f : p x ==> q res].
   proof.
     proc. (*$*) skip.
   abort.
