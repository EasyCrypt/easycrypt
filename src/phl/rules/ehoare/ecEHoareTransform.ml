(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowPhlGoal
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* Parameter of the ehoare transformation rule: the transformation, with
   its resolved parameters. Nothing to resolve: the same record is the rule
   argument and the node payload. *)
type ehoare_transform = {
  ehtr_tr : transform;
}

type EcCoreGoal.rule += REHoareTransform of ehoare_transform

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker: run the transformation on
   the goal's program, then state its obligations (first, in order) and the
   transformed judgement. The prefix obligations are hoare judgements from
   the boolean part [P] of the precondition [P `|` f], which must have that
   form when there is one; the frame of a local equivalence is taken from
   [P] when the precondition has that form (no frame otherwise). *)
let ehoare_transform_subgoals
    (hyps : LDecl.hyps) (hs : eHoareS) (n : ehoare_transform)
=
  let env = LDecl.toenv hyps in
  let m   = fst hs.ehs_m in
  let ctxt = {
    trc_hyps = hyps;
    trc_env  = env;
    trc_me   = hs.ehs_m;
    trc_post = lazy (EcPV.PV.fv env m (ehs_po hs).inv);
    trc_exn  = false;
  } in
  let r = apply ctxt n.ehtr_tr hs.ehs_s in
  let bool_pre =
    match destr_app (ehs_pr hs).inv with
    | o, pre :: _ when f_equal o fop_interp_ehoare_form -> Some pre
    | _ -> None in
  let pre () =
    match bool_pre with
    | Some pre -> { (ehs_pr hs) with inv = pre }
    | None ->
        raise (InvalidTransform "the pre should have the form \"_ `|` _\"") in
  let obligation = function
    | OPrefixPost { opp_prefix = hd; opp_cond = cond } ->
        let cond = { (ss_inv_rebind cond m) with m } in
        f_hoareS (snd hs.ehs_m) (pre ()) hd (POE.lift cond)
    | OLossless ks ->
        f_bdHoareS (snd hs.ehs_m)
          { m; inv = f_true } ks { m; inv = f_true } FHeq { m; inv = f_r1 }
    | OExprEq o ->
        f_expr_eq r.trr_me o
    | OLocalEquiv o ->
        f_local_equiv env hs.ehs_m (snd r.trr_me) bool_pre o in
  List.map obligation r.trr_obl
  @ [f_eHoareS (snd r.trr_me) (ehs_pr hs) r.trr_s (ehs_po hs)]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). A transformation that does not apply is reported as a
   tactic error. *)
let t_ehoare_transform (r : ehoare_transform) (tc : tcenv1) =
  let hs = tc1_as_ehoareS tc in
  let sg =
    try  ehoare_transform_subgoals (FApi.tc1_hyps tc) hs r
    with InvalidTransform msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (REHoareTransform r) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareTransform n ->
         Some (EcPlRecheck.checker_of "ehoare-transform" pf_as_ehoareS
                 (fun hyps hs -> ehoare_transform_subgoals hyps hs n))
     | _ -> None)
