========================================================================
Tactic: ``while``
========================================================================

The ``while`` tactic applies to program-logic goals where the next
statement to reason about is a ``while`` loop.

Applying ``while`` replaces the original goal with proof obligations that let
you reason about the loop via an invariant (and, in some variants, a
termination variant). Intuitively, you prove that the invariant is preserved
by one iteration of the loop, and you then use the invariant to justify what
follows once the loop condition becomes false.

.. contents::
   :local:

------------------------------------------------------------------------
Variant: Hoare logic
------------------------------------------------------------------------

.. admonition:: Syntax

   ``while ({formula})``

The formula is a loop invariant. It may reference variables of the program.

Applying this form of ``while`` generates (at least) the following goals:

- **Preservation goal (one iteration):** assuming the invariant holds and the
  loop condition is true, executing the loop body re-establishes the invariant.

- **Exit/continuation goal:** you must show that the invariant holds when the
  loop is entered, and that when the loop condition becomes false, the
  invariant is strong enough to derive the desired postcondition.

.. ecproof::
   :title: Hoare logic example

   require import AllCore.

   module M = {
     proc sumsq(n : int) : int = {
       var x, i;
       x <- 0;
       i <- 0;
       while (i < n) {
         x <- x + (i + 1);
         i <- i + 1;
       }
       return x;
     }
   }.

   lemma ex_while_hl (n : int) :
     hoare [M.sumsq : 0 <= n ==> 0 <= res].
   proof.
     proc.
     (*$*) while (0 <= i <= n /\ 0 <= x).
     - admit.
     - admit.
   qed.

------------------------------------------------------------------------
Variant: Probabilistic relational Hoare logic (one-sided)
------------------------------------------------------------------------

.. admonition:: Syntax

   ``while {side} {formula} {expr}``

Here `{formula}` is a relational invariant, and `{expr}` is an integer-valued
termination variant. This variant applies when the designated program by
``{side}`` ends with a `while` loop.

Applying this form of ``while`` generates two main goals:

- **Loop-body goal (designated side):** assuming the invariant holds and the
  loop condition is true, executing the loop body re-establishes the
  invariant and decreases the variant.

- **Remaining relational goal:** the loop is removed from the designated
  program, and the postcondition is strengthened with the invariant together
  with pure logical conditions connecting loop exit to the desired
  postcondition.

.. ecproof::
   :title: Relational example (shape)

   require import AllCore.

   module M = {
     proc sumsq(n : int) : int = {
       var x, i;
       x <- 0;
       i <- 0;
       while (i < n) {
         x <- x + (i + 1);
         i <- i + 1;
       }
       return x;
     }
   }.

   lemma ex_while_prhl :
     equiv [ M.sumsq ~ M.sumsq : ={n} ==> res{1} = res{2} ].
   proof.
     proc.
     (*$*) while{1} (true) (0).
     - admit.
     - admit.
   qed.

------------------------------------------------------------------------
Variant: Probabilistic Hoare logic
------------------------------------------------------------------------

.. admonition:: Syntax

   ``while {formula} {expr}``

Here ``{formula}`` is an invariant and ``{expr}`` is an integer termination
variant.

At a high level, this variant generates obligations analogous to the
designated relational case, but for a single program:

- a probabilistic goal for the loop body showing preservation of the
  invariant and strict progress of the variant, and

- a remaining goal for the code before the loop, whose postcondition is
  strengthened with the invariant plus pure logical conditions that connect
  loop exit to the desired postcondition.
