(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowPhlGoal
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* Parameter of the bdhoare transformation rule: the transformation, with
   its resolved parameters. Nothing to resolve: the same record is the rule
   argument and the node payload. *)
type bdhoare_transform = {
  btr_tr : transform;
}

type EcCoreGoal.rule += RBdHoareTransform of bdhoare_transform

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker: run the transformation on
   the goal's program, then state its obligations (first, in order) and the
   transformed judgement. The context is computed from the goal, so the
   checker recomputes it. *)
let bdhoare_transform_subgoals
    (hyps : LDecl.hyps) (bhs : bdHoareS) (n : bdhoare_transform)
=
  let env = LDecl.toenv hyps in
  let m   = fst bhs.bhs_m in
  let ctxt = {
    trc_hyps = hyps;
    trc_env  = env;
    trc_me   = bhs.bhs_m;
    trc_post = lazy (EcPV.PV.fv env m (bhs_po bhs).inv);
    trc_exn  = false;
  } in
  let r = apply ctxt n.btr_tr bhs.bhs_s in
  let obligation = function
    | OPrefixPost { opp_prefix = hd; opp_cond = cond } ->
        let cond = { (ss_inv_rebind cond m) with m } in
        f_hoareS (snd bhs.bhs_m) (bhs_pr bhs) hd (POE.lift cond)
    | OLossless ks ->
        f_bdHoareS (snd bhs.bhs_m)
          { m; inv = f_true } ks { m; inv = f_true } FHeq { m; inv = f_r1 }
    | OExprEq o ->
        f_expr_eq r.trr_me o
    | OLocalEquiv o ->
        f_local_equiv env bhs.bhs_m (snd r.trr_me) (Some (bhs_pr bhs).inv) o in
  List.map obligation r.trr_obl
  @ [f_bdHoareS (snd r.trr_me)
       (bhs_pr bhs) r.trr_s (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs)]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). A transformation that does not apply is reported as a
   tactic error. *)
let t_bdhoare_transform (r : bdhoare_transform) (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  let sg =
    try  bdhoare_transform_subgoals (FApi.tc1_hyps tc) bhs r
    with InvalidTransform msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (RBdHoareTransform r) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareTransform n ->
         Some (EcPlRecheck.checker_of "bdhoare-transform" pf_as_bdhoareS
                 (fun hyps bhs -> bdhoare_transform_subgoals hyps bhs n))
     | _ -> None)
