(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_bdhoare_skip] — empty statement, with [~] the goal's comparison:

     (d = 1%r)      forall &m, P => Q
     ---------------------------------  ~ is [=] or [>=]
        phoare [skip : P ==> Q] ~ d

   The premise [d = 1%r] is omitted when [d] is syntactically [1%r].
   Side conditions: the statement is empty, and [~] is [=] or [>=]
   (otherwise fails).

   Node: [RBdHoareSkip]. Checker: "bdhoare-skip". *)
val t_bdhoare_skip : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_bdhoare_skip_full] — on [phoare [skip : P ==> Q] ~ d]:
   1. the bound-changing consequence (currently
      [EcPhlConseq.t_bdHoareS_conseq_bd]) to [phoare [skip : P ==> Q] = 1%r],
      whose side condition (relating [~ d] to [= 1%r]) is closed when
      [simplify; split] does, and left open otherwise;
   2. then [t_bdhoare_skip], whose bound is now syntactically [1%r].
   Visible goals: [forall &m, P => Q], preceded by the bound side condition
   if not closed. Emits no node of its own. *)
val t_bdhoare_skip_full : backward
