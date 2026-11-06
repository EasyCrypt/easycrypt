(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameters of the equiv [pr] rule: the two observed expressions, typed
   in the final memory of each side, and their common type. Already typed,
   nothing to resolve: the same record is the rule argument and the node
   payload. *)
type equiv_pr = {
  epr_ty    : ty;       (* the common type of [epr_left] and [epr_right] *)
  epr_left  : ss_inv;   (* phi_l, observed on the left *)
  epr_right : ss_inv;   (* phi_r, observed on the right *)
}

type EcCoreGoal.rule += REquivFPr of equiv_pr

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side condition (both
   expressions have the recorded type) is part of it, so the checker
   re-validates it. The memory of the events and the value [a] are fresh at
   each call: the checker compares up to alpha-conversion. *)
let equivF_pr_subgoals (hyps : LDecl.hyps) (ef : equivF) (n : equiv_pr) =
  let env = LDecl.toenv hyps in
  if not (   EcReduction.EqTest.for_type env n.epr_ty n.epr_left.inv.f_ty
          && EcReduction.EqTest.for_type env n.epr_ty n.epr_right.inv.f_ty) then
    failwith "equivF-pr: the expressions do not have the recorded type";
  let (fl, fr) = (ef.ef_fl, ef.ef_fr) in
  let funl = Fun.by_xpath fl env in
  let funr = Fun.by_xpath fr env in
  let (penvl, penvr), (qenvl, qenvr) =
    Fun.equivF_memenv ef.ef_ml ef.ef_mr fl fr env in
  let m = EcIdent.create "&hr" in
  let argsl =
    map_ss_inv1 (pr_args_of_fun funl) (f_pvarg funl.f_sig.fs_arg (fst penvl)) in
  let argsr =
    map_ss_inv1 (pr_args_of_fun funr) (f_pvarg funr.f_sig.fs_arg (fst penvr)) in
  let a_id = EcIdent.create "a" in
  let a_f  = f_local a_id n.epr_ty in
  let pr1_ev = ss_inv_rebind (map_ss_inv1 (fun p -> f_eq p a_f) n.epr_left) m in
  let pr1 = f_pr (fst penvl) fl argsl.inv pr1_ev in
  let pr2_ev = ss_inv_rebind (map_ss_inv1 (fun p -> f_eq p a_f) n.epr_right) m in
  let pr2 = f_pr (fst penvr) fr argsr.inv pr2_ev in
  let concl_pr =
    f_forall_mems_ts_inv penvl penvr
      (map_ts_inv1 (f_forall_simpl [a_id, GTty n.epr_ty])
         (map_ts_inv1 (fun pr -> f_imp_simpl pr (f_eq_simpl pr1 pr2)) (ef_pr ef))) in
  let phi_l = ss_inv_generalize_as_left  n.epr_left  ef.ef_ml ef.ef_mr in
  let phi_r = ss_inv_generalize_as_right n.epr_right ef.ef_ml ef.ef_mr in
  let concl_po =
    f_forall_mems_ts_inv qenvl qenvr
      (map_ts_inv3 (fun phi_l phi_r po ->
           f_forall_simpl [a_id, GTty n.epr_ty]
             (f_imps_simpl [f_eq phi_l a_f; f_eq phi_r a_f] po))
         phi_l phi_r (ef_po ef)) in
  [concl_po; concl_pr]

(* -------------------------------------------------------------------- *)
let not_convertible tc = tc_error !!tc "formulas must have convertible types"

(* Rule (TCB). *)
let t_equivF_pr (r : equiv_pr) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let ef  = tc1_as_equivF tc in
  if not (   EcReduction.EqTest.for_type env r.epr_ty r.epr_left.inv.f_ty
          && EcReduction.EqTest.for_type env r.epr_ty r.epr_right.inv.f_ty) then
    not_convertible tc;
  FApi.xrule1 tc (REquivFPr r) (equivF_pr_subgoals (FApi.tc1_hyps tc) ef r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivFPr n ->
         Some (EcPlRecheck.checker_of "equivF-pr" pf_as_equivF
                 (fun hyps ef -> equivF_pr_subgoals hyps ef n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is expected to be an [equivF]. Type the two
   expressions in the final memory of their side, check that their types
   are convertible, then apply the rule. *)
let process_equivF_pr ((phi1, phi2) : pformula * pformula) (tc : tcenv1) =
  let hyps  = FApi.tc1_hyps tc in
  let ef    = tc1_as_equivF tc in
  let qenvl = snd (LDecl.hoareF ef.ef_ml ef.ef_fl hyps) in
  let qenvr = snd (LDecl.hoareF ef.ef_mr ef.ef_fr hyps) in
  let phi1  = TTC.pf_process_form_opt !!tc qenvl None phi1 in
  let phi2  = TTC.pf_process_form_opt !!tc qenvr None phi2 in
  if not (EcReduction.EqTest.for_type (LDecl.toenv hyps) phi1.f_ty phi2.f_ty) then
    not_convertible tc;
  t_equivF_pr
    { epr_ty    = phi1.f_ty;
      epr_left  = { m = ef.ef_ml; inv = phi1; };
      epr_right = { m = ef.ef_mr; inv = phi2; }; }
    tc
