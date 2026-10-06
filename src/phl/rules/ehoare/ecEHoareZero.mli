(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_ehoareS_zero] — null expectation:

     --------------------------
     ehoare [c : P ==> 0%xr]

   No premise. Side condition: the postcondition is syntactically [0%xr]
   (otherwise fails).

   Node: [REHoareSZero]. Checker: "ehoareS-zero". *)
val t_ehoareS_zero : backward

(* [t_ehoareF_zero] — same for a procedure:

     --------------------------
     ehoare [f : P ==> 0%xr]

   Node: [REHoareFZero]. Checker: "ehoareF-zero". *)
val t_ehoareF_zero : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_ehoare_zero] — [t_ehoareS_zero] or [t_ehoareF_zero], depending on the
   goal. *)
val t_ehoare_zero : backward
