.. _procstar-tactic:
========================================================================
Tactic: `proc*`
========================================================================

The `proc*` tactic applies to program-logic goals where the procedure(s)
under consideration are referred to by name rather than content. 

It replaces the procedure(s) with a statement calling that procedure.
This is useful, for example, when the goal is relational, but one of
the two procedures is abstract, while the other is concrete.
In that case no variant of `proc` can be applied, but `proc*` can,
after which things like inlining the concrete procedure can be
used to make progress.

.. admonition:: Syntax

  `proc*`

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
     (*$*) proc*.
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
     (*$*) proc*.
   abort.