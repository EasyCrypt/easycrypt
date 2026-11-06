(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowPhlGoal
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* Parameter of the hoare transformation rule: the transformation, with its
   resolved parameters. Nothing to resolve: the same record is the rule
   argument and the node payload. *)
type hoare_transform = {
  htr_tr : transform;
}

type EcCoreGoal.rule += RHoareTransform of hoare_transform

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker: run the transformation on
   the goal's program, then state its obligations (first, in order) and the
   transformed judgement. The context is computed from the goal, so the
   checker recomputes it. *)
let hoare_transform_subgoals (hyps : LDecl.hyps) (hs : sHoareS) (n : hoare_transform) =
  let env = LDecl.toenv hyps in
  let m   = fst hs.hs_m in
  let po  = hs_po hs in
  let ctxt = {
    trc_env  = env;
    trc_me   = hs.hs_m;
    trc_post = lazy (POE.fold
                       (fun fv f -> EcPV.PV.union fv (EcPV.PV.fv env m f))
                       EcPV.PV.empty po.hsi_inv);
  } in
  let r = apply ctxt n.htr_tr hs.hs_s in
  let obligation = function
    | OPrefixPost { opp_prefix = hd; opp_cond = cond } ->
        let cond = { (ss_inv_rebind cond m) with m } in
        f_hoareS (snd hs.hs_m) (hs_pr hs) hd (update_hs_ss cond po) in
  List.map obligation r.trr_obl
  @ [f_hoareS (snd r.trr_me) (hs_pr hs) r.trr_s po]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). A transformation that does not apply is reported as a
   tactic error. *)
let t_hoare_transform (r : hoare_transform) (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let sg =
    try  hoare_transform_subgoals (FApi.tc1_hyps tc) hs r
    with InvalidTransform msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (RHoareTransform r) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareTransform n ->
         Some (EcPlRecheck.checker_of "hoare-transform" pf_as_hoareS
                 (fun hyps hs -> hoare_transform_subgoals hyps hs n))
     | _ -> None)
