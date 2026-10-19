(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the equiv frame rules: the new postcondition [Q']. Already
   typed, nothing to resolve: the same record is the rule argument and the
   node payload. *)
type equiv_frame = {
  efr_post : ts_inv;
}

type EcCoreGoal.rule +=
  | REquivSFrame of equiv_frame
  | REquivFFrame of equiv_frame

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. *)
let equivS_frame_subgoals (hyps : LDecl.hyps) (es : equivS) (n : equiv_frame) =
  let env  = LDecl.toenv hyps in
  let post = ts_inv_rebind n.efr_post (fst es.es_ml) (fst es.es_mr) in
  let cond1, _, _ =
    EcPlFrame.ts_frame_cond_S ~mk_other:false
      env es (map_ts_inv2 f_imp post (es_po es)) in
  let cond2 =
    f_equivS (snd es.es_ml) (snd es.es_mr) (es_pr es) es.es_sl es.es_sr post in
  [cond1; cond2]

let equivF_frame_subgoals (hyps : LDecl.hyps) (ef : equivF) (n : equiv_frame) =
  let env  = LDecl.toenv hyps in
  let post = ts_inv_rebind n.efr_post ef.ef_ml ef.ef_mr in
  let cond1, _, _ =
    EcPlFrame.ts_frame_cond_F ~mk_other:false
      env hyps ef (map_ts_inv2 f_imp post (ef_po ef)) in
  let cond2 = f_equivF (ef_pr ef) ef.ef_fl ef.ef_fr post in
  [cond1; cond2]

(* -------------------------------------------------------------------- *)
(* Rules (TCB). *)
let t_equivS_frame (r : equiv_frame) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  FApi.xrule1 tc (REquivSFrame r)
    (equivS_frame_subgoals (FApi.tc1_hyps tc) es r)

let t_equivF_frame (r : equiv_frame) (tc : tcenv1) =
  let ef = tc1_as_equivF tc in
  FApi.xrule1 tc (REquivFFrame r)
    (equivF_frame_subgoals (FApi.tc1_hyps tc) ef r)

(* -------------------------------------------------------------------- *)
(* Checkers: rerun the core, which recomputes the variables written by both
   programs from the goal's own context. *)
let () =
  register_rule_checker
    (function
     | REquivSFrame n ->
         Some (EcPlRecheck.checker_of "equivS-frame" pf_as_equivS
                 (fun hyps es -> equivS_frame_subgoals hyps es n))
     | REquivFFrame n ->
         Some (EcPlRecheck.checker_of "equivF-frame" pf_as_equivF
                 (fun hyps ef -> equivF_frame_subgoals hyps ef n))
     | _ -> None)
