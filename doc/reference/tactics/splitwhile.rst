========================================================================
Tactic: ``splitwhile`` Tactic
========================================================================

The ``splitwhile`` tactic applies to program-logic goals where the program
contains a ``while`` loop.

It belongs to a family of tactics that operate by rewriting the program
into a semantically equivalent form. More precisely, given a loop of the
form::

  while (b) { c }

applying ``splitwhile`` with a splitting condition ``S`` rewrites the loop
into a structure where the execution is decomposed into two successive
loops.

In a nutshell, the original loop is split into:

- a first loop that executes iterations only while both the loop guard
  ``b`` and the splitting condition ``S`` hold,

- followed by a second loop that executes the remaining iterations of the
  original loop under the standard guard ``b``.

Concretely, the loop is rewritten into an equivalent program of the shape::

  while (b /\ S) { c };
  while (b)      { c }

This transformation allows the user to reason separately about an initial
phase of the loop execution where ``S`` is maintained, and a second phase
that accounts for the rest of the iterations.

Since this is a semantic-preserving program transformation, ``splitwhile``
can be used in any program component, independently of the surrounding
logic (Hoare logic, probabilistic Hoare logic, relational logics, etc.).

The splitting condition must be supplied explicitly; it is not inferred
automatically.

------------------------------------------------------------------------
Syntax
------------------------------------------------------------------------

The general form of the tactic is:

.. admonition:: Syntax

  ``splitwhile {side}? {codepos} : ({expr})``

Here:

- ``{expr}`` is the splitting condition used to restrict the first phase of
  the loop execution.

- ``{codepos}`` specifies the position of the ``while`` loop in the program
  that should be rewritten.

- ``{side}`` is optional and is used in relational goals to specify on
  which program the transformation should be applied (left or right). If
  omitted, the tactic applies to the single program under consideration.

The following example shows ``splitwhile`` on a Hoare goal. The program
increments ``x`` until it reaches ``10``. We split the loop into two phases:
an initial phase where ``x < 5`` holds, and then the remaining iterations.

.. ecproof::

   require import AllCore.

   module M = {
     proc up_to_10(x : int) : int = {
       while (x < 10) {
         x <- x + 1;
       }
       return x;
     }
   }.
 
   lemma up_to_10_correct :
     hoare [ M.up_to_10 : true ==> res = 10 ].
   proof.
     proc.
     (*$*)
     (* Split the loop at its position into:
        while (x < 10 /\ x < 5) { x <- x + 1 };
        while (x < 10)          { x <- x + 1 } *)
     splitwhile 1 : (x < 5).
 
     (* The goal is the same, but with the program rewritten. *)
     admit.
   qed.
