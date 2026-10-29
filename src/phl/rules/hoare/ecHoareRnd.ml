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
(* The hoare [rnd] rule has no parameters: it is an axiom on a single
   sampling, whose precondition is determined by the postcondition. *)
type EcCoreGoal.rule += RHoareRnd

(* -------------------------------------------------------------------- *)
(* Weakest precondition of [x <$ d] for the postcondition [post]:
     forall v, v \in d => post[x := v] *)
let hoare_rnd_wp env ((lv, d) : lvalue * expr) (post : ss_inv) : ss_inv =
  let m     = post.m in
  let ty    = proj_distr_ty env (e_ty d) in
  let x_id  = EcIdent.create (symbol_of_lv lv) in
  let x     = { m; inv = f_local x_id ty } in
  let d     = ss_inv_of_expr m d in
  let post  = subst_form_lv env lv x post in
  let post  = map_ss_inv2 f_imp (map_ss_inv2 f_in_supp x d) post in
  map_ss_inv1 (f_forall_simpl [(x_id, GTty ty)]) post

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   statement is a single sampling, the precondition is its weakest
   precondition) are part of it, so the checker re-validates them. *)
let hoare_rnd_subgoals (hyps : LDecl.hyps) (hs : sHoareS) : form list =
  let env = LDecl.toenv hyps in
  let rnd =
    match hs.hs_s.s_node with
    | [{ i_node = Srnd (lv, d) }] -> (lv, d)
    | _ -> failwith "hoare-rnd: the statement is not a single sampling" in
  let wp = hoare_rnd_wp env rnd (POE.lower (hs_po hs)) in
  if not (EcReduction.ss_inv_alpha_eq hyps wp (hs_pr hs)) then
    failwith "hoare-rnd: the precondition is not the expected one";
  []

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_hoare_rnd (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let sg =
    try  hoare_rnd_subgoals (FApi.tc1_hyps tc) hs
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc RHoareRnd sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareRnd ->
         Some (EcPlRecheck.checker_of "hoare-rnd" pf_as_hoareS
                 (fun hyps hs -> hoare_rnd_subgoals hyps hs))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): on [c; x <$ d], [seq] before the sampling with
   its weakest precondition as intermediate assertion, then close the
   sampling with the rule. *)
let t_hoare_rnd_last (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hs  = tc1_as_hoareS tc in
  let rnd, _ = tc1_last_rnd tc hs.hs_s in
  if not (POE.is_empty (hs_po hs).hsi_inv) then
    tc_error !!tc "exceptions are not supported";
  let mid = hoare_rnd_wp env rnd (POE.lower (hs_po hs)) in
  let at  = EcMatching.Position.gap_before_last_n 1 in
  FApi.t_seqsub
    (EcHoareSeq.t_hoare_seq { hsr_at = at; hsr_mid = mid })
    [t_id; t_hoare_rnd]
    tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareS]. [rnd] takes no side, no
   position and no argument. *)
let process_hoare_rnd
    (side : oside) (pos : psemrndpos option) (info : rnd_tac_info_f) tc
=
  match side, pos, info with
  | None, None, PNoRndParams -> t_hoare_rnd_last tc
  | _ -> tc_error !!tc "invalid arguments"
