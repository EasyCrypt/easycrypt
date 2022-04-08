(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal
open EcPhlCond

(* -------------------------------------------------------------------- *)
let process_cond info tc =
  let default_if (i : EcParsetree.codepos1 option) s =
    ofdfl (fun _ -> Zpr.cpos (tc1_pos_last_if tc s)) i in

  match info with
  | `Head side ->
    t_hS_or_bhS_or_eS
      ~th:t_hoare_cond ~tbh:t_bdhoare_cond ~te:(t_equiv_cond side) tc

  | `Seq (side, (i1, i2), f) ->
    let es = tc1_as_equivS tc in
    let f  = EcProofTyping.tc1_process_prhl_formula tc f in
    let n1 = default_if i1 es.es_sl in
    let n2 = default_if i2 es.es_sr in
    FApi.t_seqsub (EcPhlApp.t_equiv_app (n1, n2) f)
      [ t_id; t_equiv_cond side ] tc

  | `SeqOne (s, i, f1, f2) ->
    let es = tc1_as_equivS tc in
    let n = default_if i (match s with `Left -> es.es_sl | `Right -> es.es_sr) in
    let f1 = EcProofTyping.tc1_process_Xhl_formula ~side:s tc f1 in
    let f2 = EcProofTyping.tc1_process_Xhl_formula ~side:s tc f2 in
    FApi.t_seqsub
      (EcPhlApp.t_equiv_app_onesided s n f1 f2)
      [ t_id; t_bdhoare_cond] tc

(* -------------------------------------------------------------------- *)
let process_match infos tc =
  t_hS_or_bhS_or_eS ~te:(t_equiv_match infos) tc
