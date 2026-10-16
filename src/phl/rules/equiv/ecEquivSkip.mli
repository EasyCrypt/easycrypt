(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_equiv_skip] — empty statements:

       forall &1 &2, P => Q
     ---------------------------
     equiv [skip ~ skip : P ==> Q]

   Side condition: both statements are empty (otherwise fails).

   Node: [REquivSkip]. Checker: "equiv-skip". *)
val t_equiv_skip : backward
