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
Variant: Probabilistic Hoare logic with non-strict variant and `>=` or `=` bound
------------------------------------------------------------------------

This variant only works on pHL goals whose body only contains a while loop.
It can be seen as a variation of the variant pHL with `>=` bounds
with some additional requirements to handle issues with termination.

.. admonition:: Syntax

   `while {formula} {var} {varbd} {prob}`

Here `{formula}` is an invariant, `{var}` is an integer
termination variant, `{varbd}` is an upper bound on the variant, 
and `{prob}` is a lower bound on the probability that the variant decreases.

Program variables used in `{varbd}` and `{prob}` need to be unmodified by the loop body.

Though this tactic can be used to prove non-`1%r` bounds, it only works with
almost certain termination. The bounds are proven using co-induction, 
similarly to the variant of while for pHL with `>=` bounds. Using this
requires carefully setting up the precondition and bounds to facilitate this.

The tactic generates 6 goals

- A goal that connects the precondition to the invariant

- A goal that handles the case where the loop is never entered, connecting
  the bound of the pHL statement to both the precondition and postcondition.

- A goal requiring that `{varbd}` bounds the variant from above, and that the loop
  condition fails when the variant reaches 0.

- A goal requiring that the pHL holds from coinduction.

- A goal requiring that the invariant is always preserved

- A goal requiring that `{prob}` is positive and lower bounds the probability of
  the variant decreasing.

.. ecproof::
   :title: Rejection sample example
   require import AllCore DBool.

   module M = {
     proc rs(c: bool) = {
       while (c) {
         c <$ {0,1};
       }
     }
   }.

   lemma L: phoare[M.rs: true ==> true] = 1%r.
   proof.
   proc.
   (*$*) while true (b2i c) 1 (1%r/2%r).
   - (* Connecting precondition to invariant *)
     done.
   - (* Connecting precondition to pHL bound and postcondition
        when the loop is never entered *)
     done.
   - (* Showing that 1 bounds the variant, and that the variant
        reaching 0 means exiting the loop *)
     smt().
   - (* Using coinduction to prove that the pHL bound is as desired *)
     move => wH.
     conseq (: : >= 1%r).
     seq 1: true 1%r => //.
     + auto => />.
       smt(dboolE).
     conseq wH.
   - (* Showing that the invariant is preserved *)
     auto; smt(dboolE).
   (* Showing that the probabiliy bound on the variant decreasing
      is exactly that *)
   split.
   - smt().
   move => z.
   rnd; skip => />.
   smt(dboolE).
   qed.

The previous example is simpler and more well motivated, but does 
not fully demonstrate the power of the tactic, which we demonstrate 
with the following example.

.. ecproof::
   require import AllCore DBool.

   module M = {
     proc p(i: int, f: bool) = {
       var c;
       while (0 < i) {
         c <$ {0,1};
         if (c) {
           i <- i-1;
         } else {
           f <- false;
         }
       }
       return f;
     }
   }.

   lemma L: phoare[M.p: 0 <= i /\ f==> res] = ((2%r)^(-i)).
   proof.
   proc.
   exlim i => I.
   conseq (: 0 <= i <= I ==> f: 
     = (if f then 2%r ^ -i else 0%r)) => //.
   + smt().
   (*$*) while (i <= I) i I (1%r/2%r).
   - (* Connecting precondition to invariant *)
     done.
   - (* Connecting precondition to pHL bound and postcondition
        when the loop is never entered *)
     smt(RField.expr0).
   - (* Showing that I bounds the variant, and that the variant
        reaching 0 means exiting the loop *)
     smt().
   - (* Using coinduction to prove that the pHL bound is as desired *)
     move => wH.
     exlim i => i'.
     seq 2: f (if f then 1%r/2%r else 0%r) 
            (2%r ^ (1-i')) _ 0%r
            (0 <= i <= I /\ (f => i' = i + 1))=> //.
     + auto.
       smt(). 
     + wp.
       rnd (fun c => c = true /\ f).
       auto => /> &hr.
       rewrite dboolE.
       smt().
     + conseq wH. 
       * smt().
       smt().
     + conseq wH.
       * smt().
       smt().
     rewrite (StdBigop.Bigreal.Num.Domain.exprD) // RField.expr1 => />.
     smt(RField.unitrX).
   - (* Showing that the invariant is preserved *)
     auto; smt(dboolE).
   (* Showing that the probabiliy bound on the variant decreasing
      is exactly that *)
   split.
   - smt().
   move => z.
   wp.
   rnd.
   auto => />.
   smt(dboolE).
   qed.