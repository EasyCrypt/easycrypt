(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module PT  = EcProofTerm
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameter of the ehoare [exists] elimination rules: the maximal number
   of binders to eliminate ([None]: all of them, see
   [EcPlExists.prenex_exists]). Nothing to resolve: the same record is the
   rule argument and the node payload. *)
type ehoare_exists_elim = {
  ehxe_bound : int option;
}

type EcCoreGoal.rule +=
  | REHoareSExistsElim of ehoare_exists_elim
  | REHoareFExistsElim of ehoare_exists_elim

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rules and their checkers. *)
let ehoareS_exists_elim_subgoals (hs : eHoareS) (n : ehoare_exists_elim) =
  let pre = ehs_pr hs in
  let bd, inv = EcPlExists.prenex_exists ?bound:n.ehxe_bound pre.inv in
  [f_forall bd
     (f_eHoareS (snd hs.ehs_m) { pre with inv } hs.ehs_s (ehs_po hs))]

let ehoareF_exists_elim_subgoals (hf : eHoareF) (n : ehoare_exists_elim) =
  let pre = ehf_pr hf in
  let bd, inv = EcPlExists.prenex_exists ?bound:n.ehxe_bound pre.inv in
  [f_forall bd (f_eHoareF { pre with inv } hf.ehf_f (ehf_po hf))]

(* -------------------------------------------------------------------- *)
(* Rules (TCB). *)
let t_ehoareS_exists_elim (r : ehoare_exists_elim) (tc : tcenv1) =
  let hs = tc1_as_ehoareS tc in
  FApi.xrule1 tc (REHoareSExistsElim r) (ehoareS_exists_elim_subgoals hs r)

let t_ehoareF_exists_elim (r : ehoare_exists_elim) (tc : tcenv1) =
  let hf = tc1_as_ehoareF tc in
  FApi.xrule1 tc (REHoareFExistsElim r) (ehoareF_exists_elim_subgoals hf r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareSExistsElim n ->
         Some (EcPlRecheck.checker_of "ehoareS-exists-elim" pf_as_ehoareS
                 (fun _hyps hs -> ehoareS_exists_elim_subgoals hs n))
     | REHoareFExistsElim n ->
         Some (EcPlRecheck.checker_of "ehoareF-exists-elim" pf_as_ehoareF
                 (fun _hyps hf -> ehoareF_exists_elim_subgoals hf n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node). *)
let t_ehoare_exists_elim (r : ehoare_exists_elim) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FeHoareS _ -> t_ehoareS_exists_elim r tc
  | FeHoareF _ -> t_ehoareF_exists_elim r tc
  | _          -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc

(* The consequence rule, whose premise on the precondition is closed by
   [xle_cxr_l] and the values of [fs] as witnesses.

   TEMPORARY: the consequence rule still comes from the not-yet-migrated
   [EcPhlConseq]. *)
let t_ehoare_exists_intro (fs : ss_inv list) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let xs   = EcPlExists.intro_binders (List.map (fun f -> Inv_ss f) fs) in
  let pre  = EcPlExists.intro_pre ~ehoare:true xs (tc1_get_pre tc) in
  let m    = LDecl.fresh_id hyps "&m" in
  let args = List.map (fun f -> PAFormula (ss_inv_rebind f m).inv) fs in
  let t_pre =
    FApi.t_seq
      (t_intros_i [m])
      (FApi.t_seqsub
         (EcHiGoal.t_apply_prept
            (PT.Prept.uglob EcCoreLib.CI_Xreal.p_xle_cxr_l))
         [FApi.t_seq (t_exists_intro_s args) t_trivial; t_trivial]) in
  FApi.t_seqsub
    (EcPhlConseq.t_conseq pre (tc1_get_post tc))
    [t_pre; t_trivial; t_id]
    tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [eHoareS] or an [eHoareF]. *)
let process_ehoare_exists_intro
    ~(elim : bool) (fs : EcParsetree.pformula list) (tc : tcenv1)
=
  let hyps, concl = FApi.tc1_flat tc in
  let penv, m =
    match concl.f_node with
    | FeHoareF hf -> fst (LDecl.hoareF hf.ehf_m hf.ehf_f hyps), hf.ehf_m
    | FeHoareS hs -> LDecl.push_active_ss hs.ehs_m hyps, fst hs.ehs_m
    | _ -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc in
  let fs =
    List.map
      (fun f -> { m; inv = TTC.pf_process_form_opt !!tc penv None f })
      fs in
  if elim then
    FApi.t_seq
      (t_ehoare_exists_intro fs)
      (t_ehoare_exists_elim { ehxe_bound = Some (List.length fs) })
      tc
  else t_ehoare_exists_intro fs tc
