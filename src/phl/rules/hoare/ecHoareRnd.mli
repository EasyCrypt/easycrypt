(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_hoare_rnd] — single sampling:

     ----------------------------------------------------------
     hoare [x <$ d : (forall v, v \in d => Q[x := v]) ==> Q | E]

   The exceptional postconditions [E] play no role: a sampling raises
   nothing. Side conditions: the statement is the single sampling
   [x <$ d], and the precondition is, up to alpha-conversion, the one
   displayed (otherwise fails).

   Node: [RHoareRnd]. Checker: "hoare-rnd". *)
val t_hoare_rnd : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_hoare_rnd_last] — on [hoare [c; x <$ d : P ==> Q]] (no exceptional
   postcondition), with R := forall v, v \in d => Q[x := v]:
   1. [EcHoareSeq.t_hoare_seq] before the sampling, with intermediate
      assertion [R], giving
        (a) hoare [c : P ==> R]               — left open,
        (b) hoare [x <$ d : R ==> Q];
   2. [t_hoare_rnd] closes (b).
   Visible goal: (a). Fails if the last instruction is not a sampling, or
   if the goal has exceptional postconditions. Emits no node of its own. *)
val t_hoare_rnd_last : backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [rnd] on a [hoareS] goal: no side, no position, no argument. Applies
   [t_hoare_rnd_last]. *)
val process_hoare_rnd :
  oside -> psemrndpos option -> rnd_tac_info_f -> backward
