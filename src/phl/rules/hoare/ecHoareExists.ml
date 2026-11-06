(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameter of the hoare [exists] elimination rules: the maximal number
   of binders to eliminate ([None]: all of them, see
   [EcPlExists.prenex_exists]). Nothing to resolve: the same record is the
   rule argument and the node payload. *)
type hoare_exists_elim = {
  hxe_bound : int option;
}

type EcCoreGoal.rule +=
  | RHoareSExistsElim of hoare_exists_elim
  | RHoareFExistsElim of hoare_exists_elim

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rules and their checkers. *)
let hoareS_exists_elim_subgoals (hs : sHoareS) (n : hoare_exists_elim) =
  let pre = hs_pr hs in
  let bd, inv = EcPlExists.prenex_exists ?bound:n.hxe_bound pre.inv in
  [f_forall bd (f_hoareS (snd hs.hs_m) { pre with inv } hs.hs_s (hs_po hs))]

let hoareF_exists_elim_subgoals (hf : sHoareF) (n : hoare_exists_elim) =
  let pre = hf_pr hf in
  let bd, inv = EcPlExists.prenex_exists ?bound:n.hxe_bound pre.inv in
  [f_forall bd (f_hoareF { pre with inv } hf.hf_f (hf_po hf))]

(* -------------------------------------------------------------------- *)
(* Rules (TCB). *)
let t_hoareS_exists_elim (r : hoare_exists_elim) (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  FApi.xrule1 tc (RHoareSExistsElim r) (hoareS_exists_elim_subgoals hs r)

let t_hoareF_exists_elim (r : hoare_exists_elim) (tc : tcenv1) =
  let hf = tc1_as_hoareF tc in
  FApi.xrule1 tc (RHoareFExistsElim r) (hoareF_exists_elim_subgoals hf r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareSExistsElim n ->
         Some (EcPlRecheck.checker_of "hoareS-exists-elim" pf_as_hoareS
                 (fun _hyps hs -> hoareS_exists_elim_subgoals hs n))
     | RHoareFExistsElim n ->
         Some (EcPlRecheck.checker_of "hoareF-exists-elim" pf_as_hoareF
                 (fun _hyps hf -> hoareF_exists_elim_subgoals hf n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node). *)
let t_hoare_exists_elim (r : hoare_exists_elim) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FhoareS _ -> t_hoareS_exists_elim r tc
  | FhoareF _ -> t_hoareF_exists_elim r tc
  | _         -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc

(* The consequence rule, whose premise on the precondition is closed by
   giving the values of [fs] as witnesses.

   TEMPORARY: the consequence rule still comes from the not-yet-migrated
   [EcPhlConseq]. *)
let t_hoare_exists_intro (fs : ss_inv list) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let xs   = EcPlExists.intro_binders (List.map (fun f -> Inv_ss f) fs) in
  let pre  = EcPlExists.intro_pre ~ehoare:false xs (tc1_get_pre tc) in
  let h    = LDecl.fresh_id hyps "h" in
  let m    = LDecl.fresh_id hyps "&m" in
  let args = List.map (fun f -> PAFormula (ss_inv_rebind f m).inv) fs in
  let t_pre =
    FApi.t_seqs [t_intros_i [m; h]; t_exists_intro_s args; t_apply_hyp h] in
  FApi.t_seqsub
    (EcPhlConseq.t_conseq pre (tc1_get_post tc))
    [t_pre; t_trivial; t_id]
    tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareS] or a [hoareF]. *)
let process_hoare_exists_intro
    ~(elim : bool) (fs : EcParsetree.pformula list) (tc : tcenv1)
=
  let hyps, concl = FApi.tc1_flat tc in
  let penv, m =
    match concl.f_node with
    | FhoareF hf -> fst (LDecl.hoareF hf.hf_m hf.hf_f hyps), hf.hf_m
    | FhoareS hs -> LDecl.push_active_ss hs.hs_m hyps, fst hs.hs_m
    | _ -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc in
  let fs =
    List.map
      (fun f -> { m; inv = TTC.pf_process_form_opt !!tc penv None f })
      fs in
  if elim then
    FApi.t_seq
      (t_hoare_exists_intro fs)
      (t_hoare_exists_elim { hxe_bound = Some (List.length fs) })
      tc
  else t_hoare_exists_intro fs tc
