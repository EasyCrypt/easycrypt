(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type bdhoare_frame = {
  bfr_post : ss_inv;   (* new postcondition Q' *)
}

(* [t_bdhoareS_frame { bfr_post = Q' }] — framed change of the
   postcondition, with [~] the goal's comparison:

     forall &m, P => forall (mod c), Q [~>] Q'
     phoare [c : P ==> Q'] ~ d
     -----------------------------------------
          phoare [c : P ==> Q] ~ d

   where [mod c] are the program variables and globals written by [c], and
   [Q [~>] Q'] is [Q => Q'] for [<=], [Q <=> Q'] for [=], [Q' => Q] for [>=].

   Node: [RBdHoareSFrame { bfr_post = Q' }]. Checker: "bdhoareS-frame"; it
   recomputes [mod c] from the goal's context. *)
val t_bdhoareS_frame : bdhoare_frame -> backward

(* [t_bdhoareF_frame { bfr_post = Q' }] — same for a procedure [f], also
   quantifying over its result:

     forall &m, P => forall (res : ret) (mod f), (Q [~>] Q')[res/result]
     phoare [f : P ==> Q'] ~ d
     -------------------------------------------------------------------
                       phoare [f : P ==> Q] ~ d

   Node: [RBdHoareFFrame { bfr_post = Q' }]. Checker: "bdhoareF-frame". *)
val t_bdhoareF_frame : bdhoare_frame -> backward
