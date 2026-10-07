(* -------------------------------------------------------------------- *)
open EcParsetree
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Dispatch on the goal kind only; each logic owns its surface-syntax
   handling and takes the whole parse info. *)
let process_cond (info : pcond_info) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FhoareS   _ -> EcHoareIf.process_hoare_if     info tc
  | FeHoareS  _ -> EcEHoareIf.process_ehoare_if   info tc
  | FbdHoareS _ -> EcBdHoareIf.process_bdhoare_if info tc
  | FequivS   _ -> EcEquivIf.process_equiv_if     info tc
  | _ ->
      let kinds =
        match info with
        | `Head _ ->
            [`Hoare `Stmt; `EHoare `Stmt; `PHoare `Stmt; `Equiv `Stmt]
        | `Seq _ | `SeqOne _ ->
            [`Equiv `Stmt] in
      tc_error_noXhl ~kinds !!tc

(* -------------------------------------------------------------------- *)
(* There is no ehoare [match] tactic. *)
let process_match (infos : matchmode) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FhoareS   _ -> EcHoareMatch.process_hoare_match     infos tc
  | FbdHoareS _ -> EcBdHoareMatch.process_bdhoare_match infos tc
  | FequivS   _ -> EcEquivMatch.process_equiv_match     infos tc
  | _ ->
      tc_error_noXhl ~kinds:[`Hoare `Stmt; `PHoare `Stmt; `Equiv `Stmt] !!tc
