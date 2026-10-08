(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowPhlGoal
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* Parameters of the equiv transformation rule: the transformed side and
   the transformation, with its resolved parameters. Nothing to resolve:
   the same record is the rule argument and the node payload. *)
type equiv_transform = {
  etr_side : side;
  etr_tr   : transform;
}

type EcCoreGoal.rule += REquivTransform of equiv_transform

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker: run the transformation on
   the program of the chosen side, then state its obligations (first, in
   order) and the transformed judgement; the other program and memory are
   unchanged. The obligations are hoare judgements on that side, with the
   relation generalized over the other memory. *)
let equiv_transform_subgoals
    (hyps : LDecl.hyps) (es : equivS) (n : equiv_transform)
=
  let env = LDecl.toenv hyps in
  let side = n.etr_side in
  let me, mo, s =
    match side with
    | `Left  -> es.es_ml, es.es_mr, es.es_sl
    | `Right -> es.es_mr, es.es_ml, es.es_sr in
  let m = fst me in
  let ctxt = {
    trc_hyps = hyps;
    trc_env  = env;
    trc_me   = me;
    trc_post = lazy (EcPV.PV.fv env m (es_po es).inv);
    trc_exn  = false;
  } in
  let r = apply ctxt n.etr_tr s in
  let ts_inv_lower_side2 =
    sideif side ts_inv_lower_left2 ts_inv_lower_right2 in
  let ss_inv_generalize_other =
    sideif side ss_inv_generalize_right ss_inv_generalize_left in
  let obligation = function
    | OPrefixPost { opp_prefix = hd; opp_cond = cond } ->
        let cond = { (ss_inv_rebind cond m) with m } in
        let cond = ss_inv_generalize_other cond (fst mo) in
        f_forall_mems_ss_inv (EcIdent.create "&m", snd mo)
          (ts_inv_lower_side2 (fun pr po ->
             let mhs = EcIdent.create "&hr" in
             let pr  = ss_inv_rebind pr mhs in
             let po  = ss_inv_rebind po mhs in
             f_hoareS (snd me) pr hd (POE.lift po)) (es_pr es) cond)
    | OLossless ks ->
        f_bdHoareS (snd me)
          { m; inv = f_true } ks { m; inv = f_true } FHeq { m; inv = f_r1 }
    | OExprEq o ->
        f_expr_eq r.trr_me o
    | OLocalEquiv o ->
        f_local_equiv env me (snd r.trr_me) (Some (es_pr es).inv) o in
  let concl =
    match side with
    | `Left  ->
        f_equivS (snd r.trr_me) (snd es.es_mr) (es_pr es) r.trr_s es.es_sr (es_po es)
    | `Right ->
        f_equivS (snd es.es_ml) (snd r.trr_me) (es_pr es) es.es_sl r.trr_s (es_po es) in
  List.map obligation r.trr_obl @ [concl]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). A transformation that does not apply is reported as a
   tactic error. *)
let t_equiv_transform (r : equiv_transform) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let sg =
    try  equiv_transform_subgoals (FApi.tc1_hyps tc) es r
    with InvalidTransform msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (REquivTransform r) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivTransform n ->
         Some (EcPlRecheck.checker_of "equiv-transform" pf_as_equivS
                 (fun hyps es -> equiv_transform_subgoals hyps es n))
     | _ -> None)
