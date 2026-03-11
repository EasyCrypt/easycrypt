========================================================================
Tactic: ``async while`` Tactic
========================================================================

The ``async while`` tactic applies to probabilistic relational Hoare Logic
goals  where the programs contains a ``while`` loop.
Unlike the ``while`` tactic, the ``async while`` tactic allows to reason
on loops which are not in lockstep.

------------------------------------------------------------------------
Syntax
------------------------------------------------------------------------

The general form of the tactic is:

.. admonition:: Syntax

  ``async while [f1,k1] [f2,k2] (L1) (L2) : (I)``

Here:

- ``L1`` and  ``L2`` are the left and right condition to control if we
  consider the lockstep case, or the oneside case,
- ``k1`` and ``k2`` are natural number
- ``f1`` and ``f2`` are the unrolling condition, initial by the parameter
  ``k1`` and ``k2``.

Concretely, the tactic implements the following rule::

  I => (b1 <=> b2 /\ (!L1 /\ !L2 => f1 k1 /\ f2 k2)) \/ (L1 /\ b1) \/ (L2 /\ b2)
     equiv[ while (b1 /\ f1 k1) {c1} ~ while (b2 /\ f2 k2) {c2}:
            I /\ b1 <=> b2 /\ !L1 /\ !L2 /\ f1 k1 /\ f2 k2 ==> I ]
                     hoare[ c1: I /\ b1 /\ L1 /\ ==> I ]
                     hoare[ c2: I /\ b2 /\ L2 /\ ==> I ]
                phoare[ while b1 {c1}: I /\ b1 /\ L1 /\ ==> True ]
                phoare[ while b2 {c2}: I /\ b2 /\ L2 /\ ==> True ]
                  (Pre => I) /\  (I /\ !b1 /\ !b2  => Post)
  -------------------------------------------------------------------------------
               equiv[while b1 {c1} ~ while b2 {c2}:  Pre ==> Post]

The following example shows ``async while`` on a prhl goal. The program
increments ``x`` until it reaches ``10``.

.. ecproof::

  require import AllCore.

   module M = {
     proc up_to_10(x : int) : int = {
       while (x < 10) {
         x <- x + 1;
       }
       return x;
     }
     proc up_to_10_by_2(x : int) : int = {
       while (x < 10) {
         x <- x + 1;
         if ( x < 10)  x <- x + 1;
       }
       return x;
     }

   }.

   lemma asynctwhile_example :
   equiv[M.up_to_10 ~ M.up_to_10_by_2 : ={x} ==> ={res}].
   proof.
     proc.
     async while
     [ (fun r => x <= r + 1), (x{1} ) ]
     [ (fun r => x <= r ), (x{2} ) ]
     (!(x{1} < 10)) (!(x{2} < 10))
     :  (x{1} = x{2}).
       + move=> &1 &2 => /#.
       + move => v1 v2 //=.
         unroll {1} 1.
         unroll {1} 2.
         unroll {2} 1.
         rcondt {1} 1; auto.
         rcondt {2} 1; auto.
         sp 1 1.
         if => //.
         sp 1 1.
         while (!(x{1} < 10 /\ (x{1} < 10 /\ (x{1} <= v1 + 1))) /\
         !(x{2} < 10 /\ (x{2} < 10 /\ (x{2} <= v2 )))  /\ ={x}); auto => /#.
         while (!(x{1} < 10 /\ (x{1} < 10 /\ (x{1} <= v1 + 1))) /\
         !(x{2} < 10 /\ (x{2} < 10 /\ (x{2} <= v2 )))  /\ ={x}); auto => /#.
       + move => &2; exfalso=> &1 ? /#.
       + move => &1; exfalso=> &2 ? /#.
       + exfalso => /#.
       + exfalso  => /#.
       + by auto.
   qed.
