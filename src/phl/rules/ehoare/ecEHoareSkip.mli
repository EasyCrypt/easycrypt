(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_ehoare_skip] — empty statement:

        forall &m, Q <= P
     ------------------------
     ehoare [skip : P ==> Q]

   ([<=] on extended reals.) Side condition: the statement is empty
   (otherwise fails).

   Node: [REHoareSkip]. Checker: "ehoare-skip". *)
val t_ehoare_skip : backward
