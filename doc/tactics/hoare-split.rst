========================================================================
Tactic: `hoare split`
========================================================================

The `hoare split` tactic applies to **Hoare-logic goals only** whose
postcondition is a conjunction.

In this situation, the program is required to establish *all* components of
the postcondition. The `hoare split` tactic makes this explicit by splitting
the original goal into independent Hoare goals, one for each conjunct.

Applying `hoare split` does not modify the program or the precondition. It
only decomposes the logical structure of the postcondition.

.. note::

   The `hoare split` tactic is new and subject to change. Its interface and
   behavior may evolve in future versions of EasyCrypt.

.. contents::
   :local:

------------------------------------------------------------------------
Syntax
------------------------------------------------------------------------

.. admonition:: Syntax

   `hoare split`

This tactic takes no arguments. It can be applied whenever the conclusion
of a Hoare goal is a conjunction.

------------------------------------------------------------------------
Example
------------------------------------------------------------------------

.. ecproof::
   :title: Splitting a conjunctive postcondition

   require import AllCore.

   module M = {
     proc incr(x : int) : int = {
       var y : int;
       y <- x + 1;
       return y;
     }
   }.

   lemma L (n : int) : 0 <= n =>
     hoare [M.incr : x = n ==> n < res /\ 0 <= res].
   proof.
     move=> ge0_n; proc.

     (*$*) (* Split the conjunctive postcondition *)
     hoare split.

     - (* First conjunct: n < y *)
       wp; skip; smt().

     - (* Second conjunct: 0 <= y *)
       wp; skip; smt().
   qed.

------------------------------------------------------------------------
Note
------------------------------------------------------------------------

This tactic is specific to Hoare logic. An analogous transformation would be
unsound in other program logics supported by EasyCrypt (such as probabilistic
or relational program logics), where a conjunctive postcondition does not, in
general, decompose into independent proof obligations.
