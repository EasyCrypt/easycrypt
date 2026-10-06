(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_ehoare_rnd] — single sampling:

     ------------------------------------------------
     ehoare [x <$ d : Ep d (fun v => Q[x := v]) ==> Q]

   Side conditions: the statement is the single sampling [x <$ d], and the
   precondition is, up to alpha-conversion, the one displayed (otherwise
   fails).

   Node: [REHoareRnd]. Checker: "ehoare-rnd". *)
val t_ehoare_rnd : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_ehoare_rnd_last] — on [ehoare [c; x <$ d : P ==> Q]], with
   R := Ep d (fun v => Q[x := v]):
   1. [EcEHoareSeq.t_ehoare_seq] before the sampling, with intermediate
      expectation [R], giving
        (a) ehoare [c : P ==> R]              — left open,
        (b) ehoare [x <$ d : R ==> Q];
   2. [t_ehoare_rnd] closes (b).
   Visible goal: (a). Fails if the last instruction is not a sampling.
   Emits no node of its own. *)
val t_ehoare_rnd_last : backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rnd] on an [eHoareS] goal: no side, no position, no argument. Applies
   [t_ehoare_rnd_last]. *)
val process_ehoare_rnd :
  oside -> psemrndpos option -> rnd_tac_info_f -> backward
