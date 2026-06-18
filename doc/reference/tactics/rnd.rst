========================================================================
Tactic: `rnd`
========================================================================

In EasyCrypt, the `rnd` tactic is a way of reasoning about program(s)
that use random sampling statements, i.e., statements of the form 
`x <$ dX;` where `x` is an assigned variable and `dX` is a distribution.

Intuitively, the tactic exposes a probabilistic weakest precondition for
the sampling statement.
Therefore, EasyCrypt allows you to apply this rule only when the program 
ends with a sampling statement.
If the sampling appears deeper in the code, you can first use the `seq` 
tactic (or another tactic such as `wp` that eliminates the subsequent statements) 
to separate the subsequent statements from the conditional.
Samplings can also be moved earlier or later in the program using the
`swap` tactic, which can be used to reorder adjacent statements that do 
not have data dependencies.

In the one-sided setting, i.e., in (probabilistic) Hoare logic the tactic allows 
you to reason about the probability that the sampling yields a value satisfying 
a certain property (in pHL) or to simply quantify over all possible sampled
values (in HL). 
In the two-sided setting, i.e., in probabilistic relational Hoare logic, 
the tactic allows you to  couple the two samplings and establish a relation 
between the two sampled values.

.. contents::
   :local:

------------------------------------------------------------------------
Variant: `rnd` (HL)
------------------------------------------------------------------------

If the conclusion is an Hoare logic statement judgement whose program ends
    with a random assignment, then `rnd` consumes that random assignment,
    replacing the conclusion's postcondition by the possibilistic
    weakest precondition of the random assignment.

.. ecproof::
   :title: Hoare logic example

   require import AllCore Distr DBool.

   module M = {
     proc f() : bool = {
       var y : bool;

       y <$ {0,1};

       return (y && !y);
     }
   }.

   pred p : glob M.

   lemma L : hoare[M.f : p (glob M) ==> !res].
   proof.
     proc.
     (*$*)rnd.
     (* The post is now quantified over all `y`, in a context where
       `y` is known to have been sampled from the uniform distribution 
       over {0,1}. *)
     skip;smt().
   qed.


------------------------------------------------------------------------
Variant: `rnd` (pHL exact)
------------------------------------------------------------------------

If the conclusion is a probabilistic Hoare logic statement judgement whose program ends
    with a random assignment, then `rnd` consumes that random assignment,
    replacing the conclusion's postcondition by the probabilistic
    weakest precondition of the random assignment.

    This weakest precondition is defined with respect to an event `E`,
    which can be provided explicitly. When $E$ is not
    specified, it is inferred from the current postcondition.

.. ecproof::
   :title: Probabilistic Hoare logic example (exact probability)

   require import AllCore Distr DBool Real.

   module M = {
     proc f(x : bool) : bool = {
       var y : bool;

       y <$ {0,1};

       return (x = y);
     }
   }.

   pred p : glob M.

   lemma L : phoare [M.f : p (glob M) ==> res] = (1%r/2%r).
   proof.
     proc.
     (*$*)rnd (fun _y => _y = x).
        (* The post now has two clauses, the first is to prove the
           exact probability of the event, and the second one is to
           prove that the event holding is equivalent to the
           previous postcondition.  *)
     skip => *;split.
     + by exact dbool1E. 
     by smt().
   qed.

------------------------------------------------------------------------
Variant: `rnd` (pHL upper bound)
------------------------------------------------------------------------

If the conclusion is a probabilistic Hoare logic statement judgement whose program ends
    with a random assignment, then `rnd` consumes that random assignment,
    replacing the conclusion's postcondition by the probabilistic
    weakest precondition of the random assignment.

    This weakest precondition is defined with respect to an event `E`,
    which can be provided explicitly. When `E`` is not
    specified, it is inferred from the current postcondition.

.. ecproof::
   :title: Probabilistic Hoare logic example (upper bound)

   require import AllCore Distr DBool Real.

   module M = {
     proc f(x : bool) : bool = {
       var y : bool;

       y <$ {0,1};

       return (x = y);
     }
   }.

   pred p : glob M.

   lemma L : phoare [M.f : p (glob M) ==> res] <= (1%r/2%r).
   proof.
     proc.
     (*$*)rnd (fun _y => _y = x).
        (* The post now has two clauses, the first is to prove the
           probability upper bound on the event, and the second one is to
           prove that the event holding implies the
           previous postcondition. *)
     skip => *;split.
     + by smt(dbool1E). 
     by smt().
   qed.


------------------------------------------------------------------------
Variant: `rnd` (pRHL)
------------------------------------------------------------------------

In probabilistic relational Hoare logic, if the conclusion
is a judgement whose programs end with random
assignments `x1 <$ d1` and `x2 <$ d2`, and `f` and `g` are functions 
between the types of `x_1` and `x_2`, then `rnd` consumes those random 
assignments, replacing the conclusion's postcondition by the probabilistic 
weakest precondition of 
the random assignments wrt. `f` and `g`.  The new postcondition checks that:

- `f` and `g` are an isomorphism between the distributions `d1` and `d2`;
- for all elements `u` in the support of `d1`, the result of substituting `u` and `f u` for `x1` and `x2` in the conclusion's original postcondition holds.

When `g` is `f`, it can be omitted. When `f` is the identity, it
can be omitted.

.. ecproof::
   :title: Relational Hoare logic example 

    require import AllCore Distr DBool.

    module M = {
       proc f1(x : bool) : bool = {
         var y : bool;

        y <$ {0,1};

         return (x = y);
      }

      proc f2(x : bool) : bool = {
        var y : bool;

         y <$ {0,1};

        return (x = !y);
      }

    }.

    pred p : glob M.

    lemma L : equiv [M.f1 ~ M.f2 : ={x} ==> res{1} = res{2}].
    proof.
     proc.
     (*$*)rnd (fun _y => !_y).
        (* The post now has two clauses, the first is to prove that
           `f` is an involution,  and the second one is to
           prove that the previous post-condition holds under the
           coupling established by `f`. *)
     skip => *;split.
     + by smt(). 
     by smt().
    qed.




------------------------------------------------------------------------
Variant: `rnd {side}` (pRHL)
------------------------------------------------------------------------

In the one-sided `rnd` tactic used in pRHL, the user specifies whether
the random sampling to be consumed on the left or the right
program. Then, if the conclusion is a judgement whose `{side}` program 
ends with a random  assignment, the new post condition requires to prove that for 
all elements `u` in the support of the distribution, the result of substituting 
`u` for the assigned variable (in the correct `{side`} in the conclusion's 
original postcondition holds. Furthermore, the new postcondition also requires to prove 
that the sampling of the assigned variable doesn't fail, i.e. that the distribution
weight is 1. In other words, we get a possibilistic weakest precondition for 
the sampling statement on the `{side}` program.

.. ecproof::
   :title: One-sided Relational Hoare logic example 

    require import AllCore Distr DBool.

    op dB : bool distr.
    
    module M = {
       proc f1(x : bool) : bool = {
         var y : bool;

        y <$ dB;

         return (x && y);
      }

      proc f2(x : bool) : bool = {
        
        return (x);
      }

    }.

    pred p : glob M.

    lemma L :
        weight dB = 1%r =>
        equiv [M.f1 ~ M.f2 : ={x} /\ !x{1} ==> res{1} = res{2}].
    proof.
     move => HdB.
     proc.
     (*$*)rnd {1}.
        (* The post now has two clauses, the first is to prove that
           the distribution is lossless, and the second one is to
           prove that the previous post-condition holds for all possible
           sampling outputs. EasyCrypt may automatically detect that
           a losslessness assumption exists and discharges that goal
           automatically. *)
     skip => *;split.
     + by smt(). 
     by smt().
    qed.

------------------------------------------------------------------------
Variant: `rnd` (eHL)
------------------------------------------------------------------------

If the conclusion is an expectation Hoare logic statement judgement whose
program ends with a random assignment, then `rnd` consumes that random
assignment, and replaces the postcondition by the expectation of the original
postcondition in the distribution of the sampled variable.

.. ecproof::
   :title: Expectation Hoare logic example 

   require import AllCore Distr DBool Real Xreal.

   module M = {
     proc f(x : bool) : bool = {
       var y : bool;

       y <$ {0,1};

       return (x = y);
     }
   }.

   pred p : glob M.

   lemma L : ehoare [M.f : (1%r/2%r)%xr ==>  res%xr].
   proof.
     proc.
     (*$*)rnd.
        (* The post is now an expectation. *)
     skip => *;rewrite Ep_dbool;smt().
   qed.