(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcLocation
open EcTypes
open EcFol
open EcEnv
open EcMatching

module ER = EcReduction
module PT = EcProofTerm

(* -------------------------------------------------------------------- *)
type ttenv = {
  tt_engine  : ptactic_core -> FApi.backward;
  tt_provers : EcParsetree.pprover_infos -> EcProvers.prover_infos;
  tt_smtmode : [`Admit | `Strict | `Standard];
}

(* ------------------------------------------------------------------ *)
let process_apply (ff : ffpattern) (tc : tcenv1) =
  let module E = struct exception NoInstance end in

  let (hyps, concl) = FApi.tc1_flat tc in

  let rec instantiate istop pt =
    match istop && PT.can_concretize pt.PT.ptev_env with
    | true ->
        if   EcReduction.is_conv hyps pt.PT.ptev_ax concl
        then pt
        else instantiate false pt

    | false ->
        try
          PT.pf_form_match pt.PT.ptev_env ~ptn:pt.PT.ptev_ax concl;
          if not (PT.can_concretize pt.PT.ptev_env) then
            raise E.NoInstance;
          pt
        with EcMatching.MatchFailure ->
          match EcLogic.destruct_product hyps pt.PT.ptev_ax with
          | None   -> raise E.NoInstance
          | Some _ ->
              (* FIXME: add internal marker *)
              instantiate false (PT.apply_pterm_to_hole pt) in

  let pt  = instantiate true (PT.tc1_process_full_pterm tc ff) in
  let pt  = fst (PT.concretize pt) in

  EcLowGoal.t_apply pt tc

(* -------------------------------------------------------------------- *)
let process_rewrite1_core (s, o) pt tc =
  let hyps, concl = FApi.tc1_flat tc in
  let env = LDecl.toenv hyps in

  let (pt, (f1, f2)) =
    let rec find_rewrite_pattern pt =
      let ax = pt.PT.ptev_ax in

      match EcFol.sform_of_form ax with
      | EcFol.SFeq  (f1, f2) -> (pt, (f1, f2))
      | EcFol.SFiff (f1, f2) -> (pt, (f1, f2))
      | _ -> begin
        match EcLogic.destruct_product hyps ax with
        | None ->
            if   s = `LtoR && ER.EqTest.for_type env ax.f_ty tbool
            then (pt, (ax, f_true))
            else tc_error !!tc "not an equation to rewrite"
        | Some _ ->
            let pt = EcProofTerm.apply_pterm_to_hole pt in
            find_rewrite_pattern pt
      end
    in
      find_rewrite_pattern pt
  in

  let fp = match s with `LtoR -> f1 | `RtoL -> f2 in

  (try  PT.pf_find_occurence pt.PT.ptev_env ~ptn:fp concl
   with EcMatching.MatchFailure -> tc_error !!tc "nothing ot rewrite");

  let fp   = PT.concretize_form pt.PT.ptev_env fp in
  let pt   = fst (PT.concretize pt) in
  let cpos =
    try  FPosition.select_form hyps o fp concl
    with InvalidOccurence -> tc_error !!tc "invalid occurence selector"
  in

  EcLowGoal.t_rewrite pt cpos tc

(* -------------------------------------------------------------------- *)
let rec process_rewrite1 ri tc =
  match ri with
  | RWRw (s, None, o, [pt]) ->
      let pt = PT.tc1_process_full_pterm tc pt in
      process_rewrite1_core (s, o) pt tc

  | _ -> assert false

(* -------------------------------------------------------------------- *)
let process_rewrite ri tc =
  match ri with
  | [(None, ri)] -> process_rewrite1 ri tc
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let process_cut fp tc =
  EcLowGoal.t_cut (TcTyping.tc1_process_formula tc fp) tc

(* -------------------------------------------------------------------- *)
let process_reflexivity (tc : tcenv1) =
  EcLowGoal.t_reflex tc

(* -------------------------------------------------------------------- *)
let process_left (tc : tcenv1) =
  EcLowGoal.t_left tc

(* -------------------------------------------------------------------- *)
let process_right (tc : tcenv1) =
  EcLowGoal.t_right tc

(* -------------------------------------------------------------------- *)
let process_split (tc : tcenv1) =
  EcLowGoal.t_split tc

(* -------------------------------------------------------------------- *)
let process_elim (tc : tcenv1) =
  EcLowGoal.t_elim tc

(* -------------------------------------------------------------------- *)
let process1_logic (ttenv : ttenv) (t : logtactic) (tc : tcenv1) =
  let tx =
    match t with
    | Preflexivity              -> process_reflexivity
    | Papply   (ff, None)       -> process_apply   ff
    | Prewrite ri               -> process_rewrite ri
    | Pcut     (None, fp, None) -> process_cut     fp
    | Pleft                     -> process_left
    | Pright                    -> process_right
    | Psplit                    -> process_split
    | Pelim    ([], None)       -> process_elim

    | _ -> assert false
  in
    tx tc

(* -------------------------------------------------------------------- *)
let process1_phl (t : phltactic) (tc : tcenv1) =
  match t with
  | _ -> assert false
