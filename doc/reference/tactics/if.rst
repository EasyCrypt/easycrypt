========================================================================
Tactic: ``if``
========================================================================

In EasyCrypt, the ``if`` tactic is a way of reasoning about program(s)
that use conditionals. When a program begins with an if statement,
execution will follow one path if the condition is ``true`` and another
path if it is ``false``. The tactic says that to prove the program is
correct, you must consider both cases: you assume the condition holds
and show that the *then* branch establishes the desired result, and you
assume the condition does not hold and show that the *else* branch
establishes the same result. EasyCrypt allows you to apply this rule
only when the program starts with an if, so the proof can split immediately
from the initial state.If the conditional appears deeper in the code, you
can first use the seq tactic (or another tactic such as sp that eliminates
the earlier statements) to separate the preceding statements from the
conditional.

.. contents::
   :local:

------------------------------------------------------------------------
Variant: ``if`` (HL)
------------------------------------------------------------------------

.. ecproof::
   :title: Hoare logic example

   require import AllCore.

   module M = {
     proc f(x : int) = {
       var y : int;

       if (x < 0) {
         y <- -x;
       } else {
         y <- x;
       }

       return y;
     }
   }.

   pred p : glob M.

   lemma L : hoare[M.f : p (glob M) ==> 0 <= res].
   proof.
     proc.
     (*$*) if.
     (* First goal: (x < 0) holds *)
     - wp. skip. smt().
     (* Second goal: (x < 0) does not hold *)
     - wp. skip. smt().
   qed.

------------------------------------------------------------------------
Variant: ``if`` (pRHL)
------------------------------------------------------------------------

In probabilistic relational Hoare logic, the ``if`` tactic is applied
in a lock-step manner, meaning that the two programs being compared must
proceed through the conditional in sync. This requires that their guards
evaluate to the same boolean value in the related states, so that either
both programs take the *then* branch or both take the *else* branch.

As a result, using the ``if`` tactic involves establishing that the two
conditions are equal under the current relational invariant before
splitting into the two synchronized cases. 

Although synchronization ensures both guards take the same value, the
implementation splits only on the left guard (rather than explicitly
stating both are true or both are false).

.. ecproof::
   :title: Relational Hoare logic example (2-sided)

   require import AllCore.
   
   module M = {
     proc f(x : int) = {
       var y : int;
   
       if (x < 0) {
         y <- -x;
       } else {
         y <- x;
       }
   
       return y;
     }
   }.
   
   lemma L : equiv[M.f ~ M.f: x{1} = x{2} ==> res{1} = res{2}].
   proof.
     proc.
     (*$*) if.
     (* First goal: we prove that the guards are in sync. *)
     - smt().
     (* First goal: (x < 0) holds *)
     - wp; skip. smt().
     (* Second goal: (x < 0) does not hold *)
     - wp; skip. smt().
   qed.


------------------------------------------------------------------------
Variant: ``if {side}`` (pRHL)
------------------------------------------------------------------------

In the one-sided ``if`` tactic used in pRHL, the user specifies whether
the conditional reasoning should be applied to the left or the right
program. The tactic then performs a case analysis only on the ``if``
statement at the top of that chosen program, generating separate goals
for the ``true`` and ``false`` branches on that side. Unlike the lock-step
relational ``if`` tactic, no synchronization of guards is required, and
the other program is not constrained to take the same branch or even to
have a similar structure.

.. ecproof::
   :title: Relational Hoare logic example (1-sided)

   require import AllCore.
   
   module M = {
     proc f(x : int) = {
       var y : int;
   
       if (x < 0) {
         y <- -x;
       } else {
         y <- x;
       }
   
       return y;
     }
   
     proc g(x : int) = {
       return `|x|;
     }
   }.
   
   lemma L : equiv[M.f ~ M.g: x{1} = x{2} ==> res{1} = res{2}].
   proof.
     proc.
     (*$*) if{1}.
     (* First goal: (x < 0) holds (left program) *)
     - wp; skip. smt().
     (* Second goal: (x < 0) does not hold (left program) *)
     - wp; skip. smt().
   qed.

------------------------------------------------------------------------
Variant: ``if`` (pHL)
------------------------------------------------------------------------

In probabilistic Hoare logic, the ``if`` tactic behaves much like in
standard Hoare logic, except that the postcondition is expressed in terms
of a probability bound. Since the if statement is the first command of
the program, its guard is evaluated immediately in the initial state and
therefore deterministically takes either the ``true`` or the ``false``
value, with probability 1. As a result, the program execution splits into
one of the two branches without introducing any additional probabilistic
choice at the level of control flow, and the probability bound is preserved
by reasoning separately about each branch under the corresponding
assumption on the guard.

.. ecproof::
   :title: Probabilistic Hoare logic example

   require import AllCore.
   
   module M = {
     proc f(x : int) = {
       var y : int;
   
       if (x < 0) {
         y <- -x;
       } else {
         y <- x;
       }
   
       return y;
     }
   }.
   
   lemma L : phoare[M.f : true ==> 0 <= res] = 1%r.
   proof.
     proc.
     (*$*) if.
     (* First goal: (x < 0) holds *)
     - wp; skip. smt().
     (* Second goal: (x < 0) does not hold *)
     - wp; skip. smt().
   qed.

------------------------------------------------------------------------
Variant: ``if`` (eHL)
------------------------------------------------------------------------

In expectation Hoare logic, the ``if`` tactic behaves similarly to standard
Hoare logic. Two subgoals are generated, where the pre-expection is additionally
guarded by the branch condition and its negation, respectively. This naturally
splits the goal of proving the upper-bound into two cases along the control
flow.

.. ecproof::
   :title: Expectation Hoare logic example

   require import AllCore Xreal.

   module M = {
     proc f(x : int) = {
       var y : int;
   
       if (x < 0) {
         y <- -x;
       } else {
         y <- x;
       }
   
       return y;
     }
   }.

   lemma L : ehoare[M.f : 0%xr ==> (!(0 <= res))%xr].
   proof.
     proc.
     (*$*) if.
     (* First goal: (x < 0) holds *)
     - wp; skip. smt().
     (* Second goal: (x < 0) does not hold *)
     - wp; skip. smt().
   qed.
