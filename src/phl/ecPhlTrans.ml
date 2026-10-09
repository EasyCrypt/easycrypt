(* -------------------------------------------------------------------- *)
open EcParsetree
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The transitivity rules live in [rules/equiv/EcEquivTrans]: it owns their
   parameter records, pure subgoal builders, recheckable proof-nodes,
   checkers, the derived [transitivity *] form and the elaboration. This
   module only keeps the legacy positional entry points (adapters onto those
   rules, so external callers and this module's interface are unchanged) and
   the dispatcher. *)

(* -------------------------------------------------------------------- *)
let t_equivS_trans (mt, c) (p1, q1) (p2, q2) =
  EcEquivTrans.(t_equivS_trans
    { est_mt   = mt; est_stmt  = c;
      est_pre1 = p1; est_post1 = q1; est_pre2 = p2; est_post2 = q2; })

let t_equivF_trans f (p1, q1) (p2, q2) =
  EcEquivTrans.(t_equivF_trans
    { eft_f    = f;
      eft_pre1 = p1; eft_post1 = q1; eft_pre2 = p2; eft_post2 = q2; })

let t_equivS_trans_eq = EcEquivTrans.t_equivS_trans_eq

(* -------------------------------------------------------------------- *)
(* Dispatch on the goal kind only; each form owns its surface-syntax
   handling and takes the whole [trans_info]. On other goals, fail as
   before: on the surface form first, then on the goal kind it expects. *)
let process_equiv_trans ((tk, tf) as info : trans_info) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FequivS _ -> EcEquivTrans.process_equivS_trans info tc
  | FequivF _ -> EcEquivTrans.process_equivF_trans info tc
  | _ ->
      match tk, tf with
      | TKfun _, TFeq ->
          tc_error !!tc "transitivity * does not work on functions"
      | TKfun _, TFform _ ->
          tc_error_noXhl ~kinds:[`Equiv `Pred] !!tc
      | (TKstmt _ | TKparsedStmt _), _ ->
          tc_error_noXhl ~kinds:[`Equiv `Stmt] !!tc
