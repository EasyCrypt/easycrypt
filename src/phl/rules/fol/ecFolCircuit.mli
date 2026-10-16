(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_fol_circuit] — decision of a formula by circuits ([circuit] on a
   goal that is not a hoare or equiv judgement on statements):

     ------------  (no premise)
       Γ ⊢ φ

   Side conditions (otherwise fails): [Γ] binds no type variable
   (assertion); [φ] translates to a circuit (the local definitions of
   [Γ] fixing the values of their locals, the equations [x{m} = v] of
   [Γ] the values of the program variables, the other locals of [Γ] and
   the program variables of its memories being inputs) that the circuit
   backend decides valid ("Failed to solve goal through circuit
   reasoning" otherwise, "circuit solve failed with error: ..." when the
   translation fails).

   Node: [RFolCircuit]. Checker: "fol-circuit" (re-runs the decision:
   expensive, only under [EC_RECHECK]). *)
val t_fol_circuit : backward
