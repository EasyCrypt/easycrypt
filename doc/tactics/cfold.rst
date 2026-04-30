
========================================================================
Tactic: `cfold`
========================================================================

The `cfold` tactic is part of the family of tactics that operate by 
rewriting the program into a semantically equivalent form. 
More concretely, given an assignment of the form::
  
  a <- b;

the tactic propagates this (known) values of a through the program 
and inlining this (known) value whenever `a` would be used.

For example, the following excerpt::

  a <- 3;
  c <- a + 1;
  a <- a + 2;
  b <- a; 

would be converted into::

  c <- 4; (* 3 + 1 *)
  b <- 5; (* a = 3 + 2 = 5 at this point *)
  a <- 5; (* we need to make sure a has the
             correct value at the end of execution *)

.. contents::
   :local:

------------------------------------------------------------------------
Syntax
------------------------------------------------------------------------

The general form of the tactic is:

.. admonition:: Syntax

   `cfold {side}? {codepos} {n}?`

Where:

- `{side}` is optional and only applicable in relational goals
  to specify on which of the two programs the tactic is to be applied.

- `{codepos}` specifies the instruction on which the tactic will begin.
  The tactic will proceed to propagate the assignment as far as possible,
  even through other assignments to the same variable as long as it can or 
  until it reaches the line limit (if given).

- `{n}` is an optional integer argument corresponding to the number of 
  lines of the program to process in the folding. This serves to limit the 
  scope of the tactic application and prevent it from acting in the whole 
  program when this would not be desirable.

.. ecproof::
   :title: Cfold example

   require import AllCore.

   module M = {
     proc f(a : int) = {
       var x, y : int;

       x <- a + 1;
       y <- 2 * x;
       x <- 3 * y;

       return x;
     }
   }.

   lemma L : hoare[M.f : witness a ==> witness res].
   proof.
     proc.
     (*$*) cfold 1.

     (* The goal is the same but the program is now rewritten *)
     admit.
   qed.


The propagated variable is then set at the end of the part of the program 
where the tactic was applied (in this case, the end of the program, since
the tactic applied to its entirety), and it is set to the value which the 
tactic accumulated.

Here is an example of using the parameter `{n}` for limiting tactic 
application:

.. ecproof::
   :title: Cfold line restriction 

   require import AllCore.
                                                                 
   module M = {
     proc f() = {
       var x, y : int;
       var i : int;
                                                                
       i <- 0;

       while (i < 10) {
         x <- i + 1;
         y <- 2 * x;
         x <- 3 * y;
         i <- i + 1;
       }
                                                                
       return x;
     }
   }.
                                                                
   lemma L : hoare[M.f : witness ==> witness res].
   proof.
     proc.
       
     unroll for 2.
     (*$*) cfold 1 27.
     (* The goal is the same but the program is now rewritten *)
     admit.
   qed.
