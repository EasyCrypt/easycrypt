(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcTypes
open EcFol
open EcEnv
open EcLogic

(* -------------------------------------------------------------------- *)
let process_phl_form ty g phi =
  let (hyps, concl) = get_goal g in

  let m =
    match concl.f_node with
    | FhoareS   hs -> hs.hs_m
    | FbdHoareS hs -> hs.bhs_m
    | _ -> tacuerror "expecting a (bounded) hoare statement"
  in

  let hyps = LDecl.push_active m hyps in
    EcCoreHiLogic.process_form hyps phi ty

(* -------------------------------------------------------------------- *)
let process_prhl_form ty g phi =
  let (hyps, concl) = get_goal g in

  let (ml, mr) =
    match concl.f_node with
    | FequivS es -> (es.es_ml, es.es_mr)
    | _ -> tacuerror "expecting a PRHL statement"
  in

  let hyps = LDecl.push_all [ml; mr] hyps in
    EcCoreHiLogic.process_form hyps phi ty

let process_prhl_post g phi =
  let env, hyps, concl = get_goal_e g in
  let (ml, mr) =
    match concl.f_node with
    | FequivS es -> (es.es_ml, es.es_mr)
    | FequivF ef -> snd (EcEnv.Fun.equivF_memenv ef.ef_fl ef.ef_fr env)
    | _ -> tacuerror "expecting a PRHL statement" in
  let hyps = LDecl.push_all [ml; mr] hyps in
  EcCoreHiLogic.process_form hyps phi tbool
  
(* -------------------------------------------------------------------- *)
let process_phl_exp side e ty g =
  let (hyps, concl) = get_goal g in

  let (m, _) =
    try  EcFol.destr_programS side concl
    with DestrError _ -> tacuerror "conclusion not of the right form"
  in

  let hyps = LDecl.push_active m hyps in
    EcCoreHiLogic.process_exp hyps `InProc e ty

(* -------------------------------------------------------------------- *)
let process_phl_formula  = process_phl_form tbool
let process_prhl_formula = process_prhl_form tbool

let process_prhl_stmt side g c = 
  let (hyps, concl) = get_goal g in

  let es   = EcCorePhl.t_as_equivS concl in
  let mt   = snd (if side then es.es_ml else es.es_mr) in
  let hyps = LDecl.push_active (mhr,mt) hyps in
  let env  = LDecl.toenv hyps in
  let ue   = EcCoreHiLogic.unienv_of_hyps hyps in
  let c    = EcTyping.transstmt env ue c in
  let esub = Tuni.offun (EcUnify.UniEnv.close ue) in
  let esub = { e_subst_id with es_ty = esub; } in
    EcModules.s_subst esub c 
