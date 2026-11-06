(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_hoareS_true] — trivial postcondition:

     -------------------------------
     hoare [c : P ==> true | true_e]

   No premise. Side condition: every postcondition, normal and exceptional,
   is syntactically [true] (otherwise fails).

   Node: [RHoareSTrue]. Checker: "hoareS-true". *)
val t_hoareS_true : backward

(* [t_hoareF_true] — same for a procedure:

     -------------------------------
     hoare [f : P ==> true | true_e]

   Node: [RHoareFTrue]. Checker: "hoareF-true". *)
val t_hoareF_true : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_hoare_true] — [t_hoareS_true] or [t_hoareF_true], depending on the
   goal. *)
val t_hoare_true : backward
