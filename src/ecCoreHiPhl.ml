(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
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

(* -------------------------------------------------------------------- *)
let process_phl_exp side e ty g =
  let (hyps, concl) = get_goal g in

  let (m, _) =
    try  EcFol.destr_programS side concl
    with DestrError _ -> tacuerror "conclusion not of the right form"
  in

  let hyps = LDecl.push_active m hyps in
    EcCoreHiLogic.process_exp hyps e ty

(* -------------------------------------------------------------------- *)
let process_phl_formula  = process_phl_form tbool
let process_prhl_formula = process_prhl_form tbool
