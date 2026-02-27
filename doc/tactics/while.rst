========================================================================
Tactic: ``while``
========================================================================

The ``while`` tactic applies to program-logic goals where the next
statement to reason about is a ``while`` loop.

Applying ``while`` replaces the original goal with proof obligations that let
you reason about the loop via an invariant (and, in some variants, a
termination variant). Intuitively, you prove that the invariant is initially
true, is preserved by one iteration of the loop, and you then use the invariant
to justify what follows once the loop condition becomes false.

.. contents::
   :local:

------------------------------------------------------------------------
Variant: Hoare logic
------------------------------------------------------------------------

.. admonition:: Syntax

   ``while ({formula})``

The formula is a loop invariant that must hold whenever the loop condition is
evaluated (at the start of each iteration). It may reference variables of the
program.

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
termination variant. This variant applies when the program designated by
``{side}`` ends with a `while` loop.

Applying this form of ``while`` generates two main goals:

- **Loop-body goal (designated side):** assuming the invariant holds and the
  loop condition is true, executing the loop body re-establishes the
  invariant and decreases the variant with probability 1.

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
Variant: Probabilistic Hoare logic with (<=) bound
------------------------------------------------------------------------

.. admonition:: Syntax

   `while {formula}`

Here `{formula}` is a loop invariant.

This variant essentially proceeds by coinduction on the number of iterations.
A non-trivial application of this variant relies on the probability bound
depending on variables being modified by the loop. This can be achieved
by using `conseq` to change the bound.

The generated goals are as follows:

- An induction step, where you need to show that adding one more iteration 
  before a statement preserving the invariant with the bound also preserves 
  the invariant with the bound.

- A case where you show that the invariant holds to start with,
  and that the bound becomes `1%r` when the loop condition becomes false.

.. ecproof::
   :title: Probabilistic Hoare logic example (shape)

   require import AllCore DBool.

   module M = {
     proc p() = {
       var r, f;
       r <- false;
       f <- false;
       while (!r && !f) {
         f <$ {0,1};
         r <$ {0,1};
       }
       return r && !f;
     }
   }.

   lemma L: phoare[M.p: true==> res] <= (1%r/3%r).
   proof.
     proc.
     sp.
     conseq (: : <= (if (!f) then (if (!r) then (1%r/3%r) else 1%r) else 0%r)).
     - smt().
     (*$*) while true.
     - move => IH.
       conseq (: true ==> _: <= (1%r/3%r)).
       + smt().
       seq 1: f (1%r/2%r) 0%r (1%r/2%r) (2%r/3%r) => //. 
       + seq 1: true _ 0%r 0%r _ f => //.
         * auto.
         conseq IH.
         smt().
       + rnd; auto; rewrite dboolE => //.
       seq 1: r (1%r/2%r) 1%r (1%r/2%r) (1%r/3%r) (!f) => //.
       + auto.
       + rnd; auto; rewrite dboolE => //.
       + rnd; auto; rewrite dboolE => //.
       conseq IH.
       smt().
     auto.
     smt().
   qed.

------------------------------------------------------------------------
Variant: Probabilistic Hoare logic with strict variant
------------------------------------------------------------------------
 
.. admonition:: Syntax

   `while {formula} {expr}`

Here `{formula}` is an invariant and `{expr}` is an integer termination
variant.

At a high level, this variant generates obligations analogous to the
designated relational case, but for a single program:

- a probabilistic goal for the loop body showing preservation of the
  invariant and strict progress of the variant, and

- a remaining goal for the code before the loop, whose postcondition is
  strengthened with the invariant plus pure logical conditions that connect
  loop exit to the desired postcondition.

.. ecproof::
   require import AllCore DBool.
 
   module M = {
     proc p(b, e) = {
       var r;
       r <- 1;
       while (0 < e) {
         r <- r * b;
         e <- e - 1;
       }
       return r;
     }
   }.
 
   lemma L b' e': 0<=e' => b' <> 0 => 
     phoare[M.p: (b, e) = (b', e') ==> res = b'^e'] = 1%r.
   proof.
   move => e_ge0 b_ne0.
   proc.
   sp.
   (*$*) while (r = b^(e'-e) /\ b = b' /\ 0 <= e <= e') e.
   - move => z. 
     auto. 
     smt(expr_pred).
   auto. 
   smt(expr_pred expr0).
   qed.


------------------------------------------------------------------------
Variant: Probabilistic Hoare logic with non-strict variant
------------------------------------------------------------------------

.. admonition:: Syntax

   `while {formula} {expr1} {expr2} {prob}`

Here `{formula}` is an invariant, `{expr1}` and `{expr2}` are integer
termination variants, and `{prob}` is a probability threshold.

