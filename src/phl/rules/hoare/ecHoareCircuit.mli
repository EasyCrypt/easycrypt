(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_hoare_circuit] — decision by circuits ([circuit]):

     ---------------------------  (no premise)
       hoare [c : P ==> Q | E]

   Side conditions (otherwise fails): [c] only contains assignments to
   local program variables, translatable to circuits; [E] is empty
   ("exception not supported", checked after the translation of [P] and
   [c]); every conjunct of [Q] (as in [EcPlCircuit.solve_post]) is
   valid, as decided by the circuit backend, in the state obtained by
   running [c] on the inputs, under the conjuncts of [P] that translate
   to circuits ([EcPlCircuit.process_pre]), the equations [x = v] of [P]
   and of the hypotheses fixing the initial value of [x], the local
   definitions of the context fixing their values, and the other locals
   of the context and the program variables of the memory as inputs
   ("failed to verify postcondition" otherwise, "circuit solve failed
   with error: ..." when a translation fails).

   Node: [RHoareCircuit]. Checker: "hoare-circuit" (re-runs the
   decision: expensive, only under [EC_RECHECK]). *)
val t_hoare_circuit : backward
