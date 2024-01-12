(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol

open EcParsetree
open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal
open EcPhlCond
open EcMatching.Position

(* -------------------------------------------------------------------- *)
let process_cond (info : pcond_info) tc =
  let default_if (i : codepos1 option) s =
    ofdfl (fun _ -> Zpr.cpos (tc1_pos_last_if tc s)) i in

  match info with
  | `Head (side) ->
    t_hS_or_chS_or_bhS_or_eS
      ~th:t_hoare_cond
      ~teh:t_ehoare_cond
      ~tch:(t_choare_cond None)
      ~tbh:t_bdhoare_cond
      ~te:(t_equiv_cond side) tc

  | `Seq (side, (i1, i2), f) ->
    if is_cHoareS (FApi.tc1_goal tc) then
      if side <> None || i1 <> None || i2 <> None then
        tc_error !!tc "cannot supply side or code position when goal is a choare"
      else
        let _, f = EcProofTyping.tc1_process_Xhl_formula tc f in
        t_choare_cond (Some f) tc
    else
      let env = FApi.tc1_env tc in
      let es = tc1_as_equivS tc in
      let f  = EcProofTyping.tc1_process_prhl_formula tc f in
      let i1 = Option.map (EcTyping.trans_codepos1 env) i1 in
      let i2 = Option.map (EcTyping.trans_codepos1 env) i2 in
      let n1 = default_if i1 es.es_sl in
      let n2 = default_if i2 es.es_sr in
      FApi.t_seqsub (EcPhlApp.t_equiv_app (n1, n2) f)
        [ t_id; t_equiv_cond side ] tc

  | `SeqOne (s, i, f1, f2) ->
    let env = FApi.tc1_env tc in
    let es = tc1_as_equivS tc in
    let i = Option.map (EcTyping.trans_codepos1 env) i in
    let n = default_if i (match s with `Left -> es.es_sl | `Right -> es.es_sr) in
    let _, f1 = EcProofTyping.tc1_process_Xhl_formula ~side:s tc f1 in
    let _, f2 = EcProofTyping.tc1_process_Xhl_formula ~side:s tc f2 in
    FApi.t_seqsub
      (EcPhlApp.t_equiv_app_onesided s n f1 f2)
      [ t_id; t_bdhoare_cond] tc

(* -------------------------------------------------------------------- *)
let process_match infos tc =
  t_hS_or_chS_or_bhS_or_eS ~th:(t_hoare_match) ~te:(t_equiv_match infos) tc
