(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_hoare_circuit_simplify] — simplification of the postcondition by
   circuits ([circuit simplify]):

       hoare [c : P ==> Q']
     ------------------------  Q' = simpl(Q)
       hoare [c : P ==> Q]

   where [simpl(Q)] is [Q] (normalized, operators bound to circuits
   being kept folded) in which every equality [a = b] between values of
   a type bound to a bitstring or an array is replaced by [true] when
   the circuit backend decides it valid, in the state obtained by
   running [c] on the inputs, under the conjuncts of [P] that translate
   to circuits ([EcPlCircuit.process_pre]), and kept otherwise (it may
   still hold in some states: replacing it by [false] would be unsound
   under a negation); the result is then normalized. Side conditions (otherwise fails): the
   exceptional postconditions of the goal are empty ("exceptions not
   supported"); [c] only contains assignments to local program
   variables, translatable to circuits, and so are the replaced
   equalities ("Circuit simplify failed with error: ..."). The premise
   has no exceptional postcondition.

   Node: [RHoareCircuitSimplify]. Checker: "hoare-circuit-simplify"
   (re-runs the simplification: expensive, only under [EC_RECHECK]). *)
val t_hoare_circuit_simplify : backward
