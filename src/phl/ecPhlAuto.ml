(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcModules

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
let tc_noauto_error pf ?loc () =
  tc_error pf ?loc "nothing to automatize"

(* -------------------------------------------------------------------- *)
let t_exfalso_r tc =
  let post = tc1_get_post tc in

  FApi.t_or
    EcPhlTAuto.t_core_exfalso
    (FApi.t_seqsub
       (EcPhlConseq.t_conseq f_false post)
       [t_id; t_logic_trivial; EcPhlTAuto.t_core_exfalso])
    tc

let t_exfalso = FApi.t_low0 "exfalso" t_exfalso_r

(* -------------------------------------------------------------------- *)
let prnd_info =
  let builder ty =
    let id = EcIdent.create "x" in
      f_lambda [(id, GTty ty)] f_true
  in
  EcParsetree.PSingleRndParam builder

(* -------------------------------------------------------------------- *)
let t_auto_rnd_hoare_r tc =
  EcPhlRnd.t_hoare_rnd tc

(* -------------------------------------------------------------------- *)
let t_auto_rnd_bdhoare_r tc =
  let hs = tc1_as_bdhoareS tc in

  match List.olast hs.bhs_s.s_node with
  | Some { i_node = Srnd _ } -> EcPhlRnd.t_bdhoare_rnd prnd_info tc
  | _ -> tc_noauto_error !!tc ()

(* -------------------------------------------------------------------- *)
let t_auto_rnd_equiv_r tc =
  let env = FApi.tc1_env tc in
  let es  = tc1_as_equivS tc in

  let tl  = List.olast es.es_sl.s_node |> omap i_node in
  let tr  = List.olast es.es_sr.s_node |> omap i_node in

  match tl, tr with
  | Some (Srnd (_, e1)), Some (Srnd (_, e2)) ->
      if   EcReduction.EqTest.for_type env e1.e_ty e2.e_ty
      then EcPhlRnd.wp_equiv_rnd None tc
      else tc_noauto_error !!tc ()

  | Some (Srnd _), _ -> EcPhlRnd.wp_equiv_disj_rnd `Left  tc
  | _, Some (Srnd _) -> EcPhlRnd.wp_equiv_disj_rnd `Right tc

  | _, _ -> tc_noauto_error !!tc ()

(* -------------------------------------------------------------------- *)
let t_auto_rnd_hoare   = FApi.t_low0 "auto-rnd-hoare"   t_auto_rnd_hoare_r
let t_auto_rnd_bdhoare = FApi.t_low0 "auto-rnd-bdhoare" t_auto_rnd_bdhoare_r
let t_auto_rnd_equiv   = FApi.t_low0 "auto-rnd-equiv"   t_auto_rnd_equiv_r

(* -------------------------------------------------------------------- *)
let t_auto_rnd =
  t_hS_or_bhS_or_eS
    ~th:t_auto_rnd_hoare
    ~tbh:t_auto_rnd_bdhoare
    ~te:t_auto_rnd_equiv

(* -------------------------------------------------------------------- *)
let rec t_auto_phl_r tc =
  FApi.t_seqs
    [ EcPhlWp.t_wp None;
      FApi.t_ors [ FApi.t_seq t_auto_rnd t_auto_phl_r;
                   EcPhlSkip.t_skip;
                   t_id ]]
    tc

let t_auto_phl = FApi.t_low0 "auto-phl" t_auto_phl_r

(* -------------------------------------------------------------------- *)
let t_auto_r tc =
  let subtc =
    FApi.t_ors [ EcPhlTAuto.t_hoare_true;
                 EcPhlTAuto.t_core_exfalso;
                 EcPhlPr.t_prbounded false;
                 t_auto_phl ]
  in
  FApi.t_try
    (FApi.t_seqs [ FApi.t_try (t_assumption `Conv);
                   t_progress t_id;
                   FApi.t_try (t_assumption `Conv);
                   subtc; t_logic_trivial])
    tc

let t_auto = FApi.t_low0 "auto" t_auto_r

(* -------------------------------------------------------------------- *)
let t_trivial_r tc =
  let subtc =
    FApi.t_ors [ EcPhlTAuto.t_hoare_true;
                 EcPhlTAuto.t_core_exfalso;
                 EcPhlPr.t_prbounded false;
                 EcPhlSkip.t_skip ]
  in
    EcLowGoal.t_trivial (Some (FApi.t_try subtc)) tc

(* -------------------------------------------------------------------- *)
let t_trivial = FApi.t_low0 "trivial" t_trivial_r
