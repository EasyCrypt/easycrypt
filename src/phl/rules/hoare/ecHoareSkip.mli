(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_hoare_skip] — empty statement:

          forall &m, P => Q
     ---------------------------
     hoare [skip : P ==> Q | Q_e]

   The exceptional postconditions [Q_e] play no role: [skip] raises nothing.
   Side condition: the statement is empty (otherwise fails).

   Node: [RHoareSkip]. Checker: "hoare-skip". *)
val t_hoare_skip : backward
