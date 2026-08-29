========================================================================
Tactic: ``simplify if``
========================================================================

The ``simplify if`` transformation performs an if-conversion on program
statements, i.e., it rewrites ``if`` statements into conditional
expressions. This transformation preserves the program semantics.

This conversion helps prevent the weakest precondition from growing
exponentially with the number of ``if`` statements.

To illustrate this issue, consider the following example, which shows
how the weakest precondition can grow exponentially:

.. ecproof::
   :title: Weakest precondition grows exponentially.

   require import AllCore.

   module M = {
     proc f (j:int) : int * int = {
       var i, x, y;
       x <- 0;
       y <- 0;
       i <- 0;
       while (i < 6) {
         if (i = j) x <- i;
         else y <- y + i;
         i <- i + 1;
       }
       return (x, y);
     }
   }.

   hoare fP j_: M.f : j = j_ ==> res = if 0 <= j_ < 6 then (j_, 15 - j_) else (0,15).
   proof.
     proc.
     unroll for ^while.
     (*$*) time wp. (* The size of the condition grow exponentially in the value of the bound (here 6). *)
     skip.
     move => />.
     smt().
   qed.

Since the tactic preserves semantics, it can be applied to all program
logics.

.. admonition:: Syntax

  ``simplify if side? codepos?``

The ``side`` argument is required when the goal is an ``equiv``
judgment; it specifies on which side the transformation should be
applied. The ``codepos`` argument allows you to indicate which ``if``
statement the transformation should target.

.. contents::
   :local:

------------------------------------------------------------------------
Variant: Transform at a given code position
------------------------------------------------------------------------

The tactic applies only if the branches of the selected ``if`` statement
consist solely of assignments.

.. ecproof::
   :title: Hoare logic example selecting where to apply the transformation.

   require import AllCore.

   module M = {
     proc f (j:int) : int * int = {
       var i, x, y;
       x <- 0;
       y <- 0;
       i <- 0;
       while (i < 6) {
         if (i = j) x <- i;
         else y <- y + i;
         i <- i + 1;
       }
       return (x, y);
     }
   }.

   hoare fP_simplify2 j_: M.f : j = j_ ==> res = if 0 <= j_ < 6 then (j_, 15 - j_) else (0,15).
   proof.
     proc.
     unroll for ^while.
     (* You can select a particular occurence of if using codepos *)
     (*$*) simplify if ^if. (* Apply the transformation on the first if *)
     simplify if ^if{2}.  (* Apply the transformation on the second if *)
     simplify if ^if{-2}. (* Apply the trnasformation of the penultimate if *)
     time wp.
     skip.
     move => />.
     smt().
   qed.

------------------------------------------------------------------------
Variant: Transform as much as possible
------------------------------------------------------------------------

.. admonition:: Syntax

  ``simplify if``

This variant attempts to find a position where the transformation can
be applied and applies it. The process is repeated until no applicable
position remains.

.. ecproof::
   :title: Hoare logic example.

   require import AllCore.

   module M = {
     proc f (j:int) : int * int = {
       var i, x, y;
       x <- 0;
       y <- 0;
       i <- 0;
       while (i < 6) {
         if (i = j) x <- i;
         else y <- y + i;
         i <- i + 1;
       }
       return (x, y);
     }
   }.

   hoare fP_simplify j_: M.f : j = j_ ==> res = if 0 <= j_ < 6 then (j_, 15 - j_) else (0,15).
   proof.
     proc.
     unroll for ^while.
     (*$*)simplify if. (* if instruction are transformed into single assignment *)
     time wp.  (* The size of the wp is now linear in the number of instruction *)
     skip.
     move => />.
     smt().
   qed.
