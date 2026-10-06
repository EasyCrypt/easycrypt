(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The ehoare [rnd] rule has no parameters: it is an axiom on a single
   sampling, whose precondition is determined by the postcondition. *)
type EcCoreGoal.rule += REHoareRnd

(* -------------------------------------------------------------------- *)
(* Weakest pre-expectation of [x <$ d] for the postcondition [post]:
     Ep d (fun v => post[x := v]) *)
let ehoare_rnd_wp env ((lv, d) : lvalue * expr) (post : ss_inv) : ss_inv =
  let m    = post.m in
  let ty   = proj_distr_ty env (e_ty d) in
  let x_id = EcIdent.create (symbol_of_lv lv) in
  let x    = f_local x_id ty in
  let d    = ss_inv_of_expr m d in
  let post = subst_form_lv env lv { m; inv = x } post in
  map_ss_inv2 (f_Ep ty) d (map_ss_inv1 (f_lambda [(x_id, GTty ty)]) post)

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   statement is a single sampling, the precondition is its weakest
   pre-expectation) are part of it, so the checker re-validates them. *)
let ehoare_rnd_subgoals (hyps : LDecl.hyps) (hs : eHoareS) : form list =
  let env = LDecl.toenv hyps in
  let rnd =
    match hs.ehs_s.s_node with
    | [{ i_node = Srnd (lv, d) }] -> (lv, d)
    | _ -> failwith "ehoare-rnd: the statement is not a single sampling" in
  let wp = ehoare_rnd_wp env rnd (ehs_po hs) in
  if not (EcReduction.ss_inv_alpha_eq hyps wp (ehs_pr hs)) then
    failwith "ehoare-rnd: the precondition is not the expected one";
  []

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_ehoare_rnd (tc : tcenv1) =
  let hs = tc1_as_ehoareS tc in
  let sg =
    try  ehoare_rnd_subgoals (FApi.tc1_hyps tc) hs
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc REHoareRnd sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareRnd ->
         Some (EcPlRecheck.checker_of "ehoare-rnd" pf_as_ehoareS
                 (fun hyps hs -> ehoare_rnd_subgoals hyps hs))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): on [c; x <$ d], [seq] before the sampling with
   its weakest pre-expectation as intermediate expectation, then close the
   sampling with the rule. *)
let t_ehoare_rnd_last (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hs  = tc1_as_ehoareS tc in
  let rnd, _ = tc1_last_rnd tc hs.ehs_s in
  let mid = ehoare_rnd_wp env rnd (ehs_po hs) in
  let at  = EcMatching.Position.gap_before_last_n 1 in
  FApi.t_seqsub
    (EcEHoareSeq.t_ehoare_seq { ehsr_at = at; ehsr_mid = mid })
    [t_id; t_ehoare_rnd]
    tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [eHoareS]. [rnd] takes no side,
   no position and no argument. *)
let process_ehoare_rnd
    (side : oside) (pos : psemrndpos option) (info : rnd_tac_info_f) tc
=
  match side, pos, info with
  | None, None, PNoRndParams -> t_ehoare_rnd_last tc
  | _ -> tc_error !!tc "invalid arguments"
