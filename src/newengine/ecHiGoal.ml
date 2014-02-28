(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcLocation

module PT = EcProofTerm

(* ------------------------------------------------------------------ *)
let process_apply (ff : ffpattern) (tc : tcenv) =
  let module E = struct exception NoInstance end in

  let (hyps, concl) = FApi.tc_flat tc in

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
        with EcMetaProg.MatchFailure ->
          match EcLogic.destruct_product hyps pt.PT.ptev_ax with
          | None   -> raise E.NoInstance
          | Some _ ->
              (* FIXME: add internal marker *)
              instantiate true (PT.apply_pterm_to_hole pt) in

  let pt  = instantiate true (PT.tc_process_full_pterm tc ff) in
  let pt  = fst (PT.concretize pt) in

  EcLowGoal.t_apply pt tc

(* -------------------------------------------------------------------- *)
let process1 (t : ptactic) (tc : tcenv) =
  match (unloc t.pt_core) with
  | Padmit  -> EcLowGoal.t_admit tc
  | Plogic (Papply (ff, None)) -> process_apply ff tc
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let process (t : ptactic list) (pf : proof) =
  let pf = tcenv_of_proof pf in
  let pf = FApi.lseq (List.map process1 t) pf in
    proof_of_tcenv pf
