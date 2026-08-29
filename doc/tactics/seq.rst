========================================================================
Tactic: ``seq``
========================================================================

The ``seq`` tactic applies to program-logic goals by splitting the
program(s) under consideration into two consecutive parts.

Applying ``seq`` allows one to decompose such a goal into two separate
program-logic obligations by splitting the program(s) at a chosen point.
The first obligation establishes that the initial precondition ensures
some intermediate assertion after execution of the first part. The second
obligation then shows that, assuming this intermediate assertion, execution
of the second part entails the desired postcondition.

The ``seq`` tactic requires the intermediate assertion to be supplied by
the user, it is not inferred automatically.

.. contents::
   :local:

------------------------------------------------------------------------
Variant: Hoare logic
------------------------------------------------------------------------

.. admonition:: Syntax

   ``seq {codepos} : ({formula})``

The ``{codepos}`` specifies the position in the program where the split
should occur. The formula ``{formula}`` is the intermediate assertion that
must hold after execution of the first part of the program.

Applying this form of ``seq`` produces two Hoare-style proof obligations:
one for the first segment, from the original precondition to the supplied
intermediate assertion, and one for the remaining segment, from this
assertion to the original postcondition.

.. ecproof::
   :title: Hoare logic example   

   require import AllCore.

   module M = {
     proc add3(x : int) : int = {
       var y : int;
       y <- x + 1;
       y <- y + 2;
       return y;
     }
   }.
   
   lemma add3_correct (n : int) :
     hoare [M.add3 : x = n ==> res = n + 3].
   proof.
     proc.

     (*$*) (* Split after the first command, and supply an intermediate assertion. *)
     seq 1 : (y = n + 1).
   
     - (* First part: y <- x + 1 *)
       wp. skip. smt().
   
     - (* Second part: y <- y + 2; return y *)
       wp. skip. smt().
   qed.

------------------------------------------------------------------------
Variant: Probabilistic relation Hoare logic (two-sided)
------------------------------------------------------------------------

.. admonition:: Syntax

   ``seq {codepos} {codepos} : {formula}``

Here, the first ``{codepos}`` specifies where to split the left-hand
program, and the second ``{codepos}`` specifies where to split the right-hand
program. The formula ``{formula}`` is the intermediate *relational* assertion
that must hold between the two memories after execution of the first parts.

Applying this form of ``seq`` produces two relational proof obligations:
one for the initial segments of both programs, from the original precondition
to the supplied intermediate assertion, and one for the remaining segments,
from this assertion to the original postcondition.

.. ecproof::
   :title: Probabilistic relational Hoare logic example   

   require import AllCore.

   module L = {
     proc inc_then_double(x : int) : int = {
       var y, z : int;

       y <- x + 1;
       z <- y * 2;
       return z;
     }
   }.
   
   module R = {
     proc keep_then_double_as_if_inc(x : int) : int = {
       var y, z : int;

       y <- x;
       z <- (y + 1) * 2;
       return z;
     }
   }.
   
   lemma inc_then_double_equiv : equiv [
     L.inc_then_double ~ R.keep_then_double_as_if_inc :
       x{1} = x{2} ==> res{1} = res{2}
   ].
   proof.
     proc.
   
     (*$*) (* Split after the first command on both sides, and relate the intermediate states. *)
     seq 1 1 : (y{1} = y{2} + 1).
   
     - (* First parts: y <- x + 1   ~   y <- x *)
       wp. skip. smt().
   
     - (* Second parts: z <- ...; return z   ~   z <- ...; return z *)
       wp. skip. smt().
   qed.

------------------------------------------------------------------------
Variant: Probabilistic relation Hoare logic (one-sided)
------------------------------------------------------------------------

.. admonition:: Syntax

   ``seq {side} {codepos} : (_: {formula} ==> {formula})``

------------------------------------------------------------------------
Variant: Probabilistic Hoare logic
------------------------------------------------------------------------

.. admonition:: Syntax

   ``seq {codepos} : {formula} {formula|_} {formula|_} {formula|_} {formula|_} {formula}?``

Here:

- ``{codepos}`` specifies where the program is split into a first and a
  second part.
- The first ``{formula}`` is the probabilistic intermediate assertion,
  used to connect the probability reasoning between the two parts of the
  program.
- The four arguments ``{formula|_}`` are the real probability bounds required
  by the probabilistic sequencing rule. Each may be given explicitly, or left
  as ``_`` to let EasyCrypt infer or simplify it.
- The last optional ``{formula}`` is a non-probabilistic intermediate
  assertion that is required to hold after execution of the first part.
  When provided, it is added to the preconditions of the subgoals targeting
  the second part of the program.

The four real coefficients supplied to ``seq`` correspond to the two possible
outcomes of the intermediate probabilistic assertion:

- The **first coefficient** bounds the probability that the intermediate
  assertion holds after executing the first part of the program.

- The **second coefficient** bounds the probability of reaching the final
  postcondition after executing the second part, assuming the intermediate
  assertion holds.

- The **third coefficient** bounds the probability that the intermediate
  assertion does *not* hold after the first part.

- The **fourth coefficient** bounds the probability of reaching the final
  postcondition after the second part, assuming the intermediate assertion
  does not hold.

These coefficients are then combined in the final arithmetic goal to obtain
the probability bound of the original judgement.

When `seq` is applied to a probabilistic Hoare-logic goal, EasyCrypt splits
the program into two parts and generates several proof obligations that
justify how the probability of the whole program is obtained from the two
fragments.

Concretely, the tactic produces the following kinds of goals:

- **A Hoare goal for the optional pure assertion**. 
  If a final (non-probabilistic) intermediate assertion is provided, the
  first goal is to prove that the first part of the program establishes this
  assertion from the current precondition. If no assertion is given, it is
  taken to be `true`, and this goal is trivial.

- **A probabilistic goal for the first part**.
  A goal is generated to bound the probability that the first part of the
  program establishes the intermediate probabilistic assertion.

- **Probabilistic goals for the second part under the intermediate assertion**.
  The second part of the program is then considered assuming that the
  intermediate probabilistic assertion holds (and also assuming the optional
  pure assertion, if one was provided). A goal is generated to bound the
  probability of reaching the final postcondition in this case.

- **Probabilistic goals for the second part under the negation of the intermediate assertion**.
  A symmetric goal is generated for the case where the intermediate
  probabilistic assertion does *not* hold after the first part.

- **A final logical side-condition combining the bounds**  
  Finally, EasyCrypt generates a pure arithmetic obligation stating that the
  probability bounds supplied to ``seq`` correctly combine to give the overall
  probability bound of the original goal.

.. ecproof::
   :title: Probabilistic Hoare logic example   

   require import AllCore Distr DInterval.
   
   module M = {
     proc two_steps() : bool = {
       var x, y : int;
   
       x <$ [0..2];
       y <$ [0..2];
       return (x <> 0) /\ (y = 2);
     }
   }.
   
   lemma two_steps_pr :
     phoare [ M.two_steps : true ==> res ] = (2%r / 9%r).
   proof.
     proc.

     (*$*)
     (* Split after the first sampling.
        Probabilistic intermediate assertion: x <> 0.
        Extra pure assertion: true (trivial here). *)
     seq 1 :
       (x <> 0)
       (2%r/3%r)   (* probability that x <> 0 *)
       (1%r/3%r)   (* probability that x <> 0 /\ y = 2 | x <> 0 *)
       (1%r/3%r)   (* probability that x = 0 *)
       (0%r)       (* probability that x <> 0 /\ y = 2 | x = 0 *)
       (true).
   
     - (* Hoare goal: first part establishes the extra assertion *)
       by auto.
   
     - 
       rnd (predC1 0). skip=> /=. split.
       - rewrite mu_not.
         rewrite dinter_ll //=.
         rewrite dinter1E /=.
         done.
       - smt().
   
     - rnd (pred1 2). skip=> &hr /= *. split.
       - by rewrite dinter1E. 
       - smt().
   
     - rnd pred0. skip=> &hr /= *. split.
       - by rewrite mu0.
       - smt().
   
     - done.
   qed.

------------------------------------------------------------------------
Variant: Expectation Hoare logic
------------------------------------------------------------------------

.. admonition:: Syntax

   ``seq {codepos} : {formula}``
