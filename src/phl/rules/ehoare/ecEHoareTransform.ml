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
   transformed judgement. The obligations are hoare judgements from the
   boolean part [P] of the precondition [P `|` f], which must have that
   form when there is an obligation. *)
let ehoare_transform_subgoals
    (hyps : LDecl.hyps) (hs : eHoareS) (n : ehoare_transform)
=
  let env = LDecl.toenv hyps in
  let m   = fst hs.ehs_m in
  let ctxt = {
    trc_env  = env;
    trc_me   = hs.ehs_m;
    trc_post = lazy (EcPV.PV.fv env m (ehs_po hs).inv);
  } in
  let r = apply ctxt n.ehtr_tr hs.ehs_s in
  let pre () =
    let pre pr =
      match destr_app pr with
      | o, pre :: _ when f_equal o fop_interp_ehoare_form -> pre
      | _ -> raise (InvalidTransform "the pre should have the form \"_ `|` _\"") in
    map_ss_inv1 pre (ehs_pr hs) in
  let obligation = function
    | OPrefixPost { opp_prefix = hd; opp_cond = cond } ->
        let cond = { (ss_inv_rebind cond m) with m } in
        f_hoareS (snd hs.ehs_m) (pre ()) hd (POE.lift cond) in
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
