(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_equiv_circuit] — decision by circuits ([circuit]):

     ----------------------------  (no premise)
       equiv [c1 ~ c2 : P ==> Q]

   Side conditions (otherwise fails): [c1] and [c2] only contain
   assignments to local program variables, translatable to circuits;
   every conjunct of [Q] (as in [EcPlCircuit.solve_post]) is valid, as
   decided by the circuit backend, in the state obtained by running [c1]
   (on the left memory) then [c2] (on the right memory) on the inputs,
   under the conjuncts of [P] that translate to circuits
   ([EcPlCircuit.process_pre]), the equations [x = v] of [P] and of the
   hypotheses fixing the initial value of [x], the local definitions of
   the context fixing their values, and the other locals of the context
   and the program variables of both memories as inputs ("failed to
   verify postcondition" otherwise, "circuit solve failed with error:
   ..." when a translation fails).

   Node: [REquivCircuit]. Checker: "equiv-circuit" (re-runs the
   decision: expensive, only under [EC_RECHECK]). *)
val t_equiv_circuit : backward
