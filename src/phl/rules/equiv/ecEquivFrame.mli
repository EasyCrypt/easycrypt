(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_frame = {
  efr_post : ts_inv;   (* new postcondition Q' *)
}

(* [t_equivS_frame { efr_post = Q' }] — framed weakening of the
   postcondition:

     forall &1 &2, P => forall (mod c)<1> (mod c')<2>, Q' => Q
     equiv [c ~ c' : P ==> Q']
     ---------------------------------------------------------
                equiv [c ~ c' : P ==> Q]

   where [mod c] / [mod c'] are the program variables and globals written by
   each side.

   Node: [REquivSFrame { efr_post = Q' }]. Checker: "equivS-frame"; it
   recomputes [mod c], [mod c'] from the goal's context. *)
val t_equivS_frame : equiv_frame -> backward

(* [t_equivF_frame { efr_post = Q' }] — same for procedures [f ~ f'], also
   quantifying over their results:

     forall &1 &2, P =>
       forall (res_L : ret) (res_R : ret') (mod f)<1> (mod f')<2>,
         (Q' => Q)[res_L/result<1>, res_R/result<2>]
     equiv [f ~ f' : P ==> Q']
     ---------------------------------------------------------------
                    equiv [f ~ f' : P ==> Q]

   Node: [REquivFFrame { efr_post = Q' }]. Checker: "equivF-frame". *)
val t_equivF_frame : equiv_frame -> backward
