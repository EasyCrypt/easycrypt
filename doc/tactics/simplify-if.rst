========================================================================
Tactic: `simplify if`
========================================================================

The `simplify if` performs an if-conversion on program statement,
i.e it transform if statement into if expression. This transformation preserves the semantics.
This allows to obtain a statement where the weakest precondition does not grow 
exponentially in the number of if. 

To illustrate the problem here is an example that show how grow the weakest pre-condition:
.. ecproof::
   :title: Weakest pre-condition grow exponentially.

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

.. admonition:: Syntax
  
  Since the tactic preserves the semantic it applies to all program logics.

  `simplify if side? codepos?`

  The `side` argument is required when the goal is a `equiv` judgment, it allows to select
  on which side you want to apply the program transformation. The `codepos` argument allows
  to specify on which `if` instruction you want to apply the transformation.


.. contents::
   :local:

------------------------------------------------------------------------
Variant: Transform at a given code possition 
------------------------------------------------------------------------
The tactic applies only if the branches of selected the `if` instruction are only composed of 
assignment. 

.. exproof::
   : title: Hoare logic example selecting where to apply the transformation
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

  `simplify if`

This variant try to find a position where the transformation is possible and applies it.
This is repeated until no position is found.

.. ecproof::
   :title: Hoare logic example

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
