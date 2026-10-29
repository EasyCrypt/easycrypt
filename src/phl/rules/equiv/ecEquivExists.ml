(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameter of the equiv [exists] elimination rules: the maximal number
   of binders to eliminate ([None]: all of them, see
   [EcPlExists.prenex_exists]). Nothing to resolve: the same record is the
   rule argument and the node payload. *)
type equiv_exists_elim = {
  exe_bound : int option;
}

type EcCoreGoal.rule +=
  | REquivSExistsElim of equiv_exists_elim
  | REquivFExistsElim of equiv_exists_elim

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rules and their checkers. *)
let equivS_exists_elim_subgoals (es : equivS) (n : equiv_exists_elim) =
  let pre = es_pr es in
  let bd, inv = EcPlExists.prenex_exists ?bound:n.exe_bound pre.inv in
  [f_forall bd
     (f_equivS (snd es.es_ml) (snd es.es_mr) { pre with inv }
        es.es_sl es.es_sr (es_po es))]

let equivF_exists_elim_subgoals (ef : equivF) (n : equiv_exists_elim) =
  let pre = ef_pr ef in
  let bd, inv = EcPlExists.prenex_exists ?bound:n.exe_bound pre.inv in
  [f_forall bd (f_equivF { pre with inv } ef.ef_fl ef.ef_fr (ef_po ef))]

(* -------------------------------------------------------------------- *)
(* Rules (TCB). *)
let t_equivS_exists_elim (r : equiv_exists_elim) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  FApi.xrule1 tc (REquivSExistsElim r) (equivS_exists_elim_subgoals es r)

let t_equivF_exists_elim (r : equiv_exists_elim) (tc : tcenv1) =
  let ef = tc1_as_equivF tc in
  FApi.xrule1 tc (REquivFExistsElim r) (equivF_exists_elim_subgoals ef r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivSExistsElim n ->
         Some (EcPlRecheck.checker_of "equivS-exists-elim" pf_as_equivS
                 (fun _hyps es -> equivS_exists_elim_subgoals es n))
     | REquivFExistsElim n ->
         Some (EcPlRecheck.checker_of "equivF-exists-elim" pf_as_equivF
                 (fun _hyps ef -> equivF_exists_elim_subgoals ef n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node). *)
let t_equiv_exists_elim (r : equiv_exists_elim) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FequivS _ -> t_equivS_exists_elim r tc
  | FequivF _ -> t_equivF_exists_elim r tc
  | _         -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc

(* The consequence rule, whose premise on the precondition is closed by
   giving the values of [fs] as witnesses.

   TEMPORARY: the consequence rule still comes from the not-yet-migrated
   [EcPhlConseq]. *)
let t_equiv_exists_intro (fs : ts_inv list) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let xs   = EcPlExists.intro_binders (List.map (fun f -> Inv_ts f) fs) in
  let pre  = EcPlExists.intro_pre ~ehoare:false xs (tc1_get_pre tc) in
  let h    = LDecl.fresh_id hyps "h" in
  let ml, mr = as_seq2 (LDecl.fresh_ids hyps ["&ml"; "&mr"]) in
  let args = List.map (fun f -> PAFormula (ts_inv_rebind f ml mr).inv) fs in
  let t_pre =
    FApi.t_seqs
      [t_intros_i [ml; mr; h]; t_exists_intro_s args; t_apply_hyp h] in
  FApi.t_seqsub
    (EcPhlConseq.t_conseq pre (tc1_get_post tc))
    [t_pre; t_trivial; t_id]
    tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivS] or an [equivF]. *)
let process_equiv_exists_intro
    ~(elim : bool) (fs : EcParsetree.pformula list) (tc : tcenv1)
=
  let hyps, concl = FApi.tc1_flat tc in
  let penv, (ml, mr) =
    match concl.f_node with
    | FequivF ef ->
        fst (LDecl.equivF ef.ef_ml ef.ef_mr ef.ef_fl ef.ef_fr hyps),
        (ef.ef_ml, ef.ef_mr)
    | FequivS es ->
        LDecl.push_all [es.es_ml; es.es_mr] hyps,
        (fst es.es_ml, fst es.es_mr)
    | _ -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc in
  let fs =
    List.map
      (fun f -> { ml; mr; inv = TTC.pf_process_form_opt !!tc penv None f })
      fs in
  if elim then
    FApi.t_seq
      (t_equiv_exists_intro fs)
      (t_equiv_exists_elim { exe_bound = Some (List.length fs) })
      tc
  else t_equiv_exists_intro fs tc
