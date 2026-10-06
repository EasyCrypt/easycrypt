(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type hoare_frame = {
  hfr_post : hs_inv;   (* new postcondition Q' (normal and exceptional) *)
}

(* [t_hoareS_frame { hfr_post = Q' }] — framed weakening of the
   postcondition:

     forall &m, P => forall (mod c), (Q' => Q) /\ (forall e, Q'_e => Q_e)
     hoare [c : P ==> Q' | Q'_e]
     ---------------------------------------------------------------------
                       hoare [c : P ==> Q | Q_e]

   where [mod c] are the program variables and globals written by [c], and
   [Q_e] / [Q'_e] the exceptional postconditions.

   Node: [RHoareSFrame { hfr_post = Q' }]. Checker: "hoareS-frame"; it
   recomputes [mod c] from the goal's context. *)
val t_hoareS_frame : hoare_frame -> backward

(* [t_hoareF_frame { hfr_post = Q' }] — same for a procedure [f], also
   quantifying over its result:

     forall &m, P =>
       forall (res : ret) (mod f), ((Q' => Q) /\ (forall e, Q'_e => Q_e))[res/result]
     hoare [f : P ==> Q' | Q'_e]
     ---------------------------------------------------------------------
                       hoare [f : P ==> Q | Q_e]

   Node: [RHoareFFrame { hfr_post = Q' }]. Checker: "hoareF-frame". *)
val t_hoareF_frame : hoare_frame -> backward
