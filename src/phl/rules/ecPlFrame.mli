(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv

(* -------------------------------------------------------------------- *)
(* Framing conditions, shared by the frame rules of every logic (and by
   [conseq auto]). Framing — generalizing a condition over the variables a
   program writes — is done here and nowhere else.

   Each builder returns [(cond, bmem, bother)]: the closed side condition,
   the memories it quantifies over, and — only when [~mk_other] — bindings
   for the other quantified variables (result, modified globals and program
   variables), used by [conseq auto] to introduce them. *)

type frame_cond = form * memory list * (EcIdent.t * ss_inv) list

(* Statement [s] in memory [memenv]:
     forall &m, pre => forall (mod s), cond *)
val ss_frame_cond_S :
  mk_other:bool -> env -> stmt -> memenv -> ss_inv -> ss_inv -> frame_cond

(* Procedure [f], postcondition memory [m]:
     forall &m, pre => forall (res : ret) (mod f), cond[res / result] *)
val ss_frame_cond_F :
  mk_other:bool -> env -> LDecl.hyps -> EcPath.xpath -> memory
  -> ss_inv -> ss_inv -> frame_cond

(* Two-sided, statements of [es], under its precondition:
     forall &1 &2, pre => forall (mod sl)<1> (mod sr)<2>, cond *)
val ts_frame_cond_S : mk_other:bool -> env -> equivS -> ts_inv -> frame_cond

(* Two-sided, procedures of [ef], under its precondition:
     forall &1 &2, pre =>
       forall (res_L : retl) (res_R : retr) (mod fl)<1> (mod fr)<2>,
         cond[res_L / result<1>, res_R / result<2>] *)
val ts_frame_cond_F :
  mk_other:bool -> env -> LDecl.hyps -> equivF -> ts_inv -> frame_cond
