(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcTypes
open EcFol
open EcEnv
open EcCoreGoal

module Msym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type ptnenv = ty Mid.t * EcUnify.unienv
type metavs = EcFol.form EcSymbols.Msym.t

(* ------------------------------------------------------------------ *)
let unienv_of_hyps hyps =
   let tv = (LDecl.tohyps hyps).EcBaseLogic.h_tvar in
   EcUnify.UniEnv.create (Some tv)

(* ------------------------------------------------------------------ *)
let process_form_opt ?mv hyps pf oty =
  try
    let ue  = unienv_of_hyps hyps in
    let ff  = EcTyping.trans_form_opt ?mv (LDecl.toenv hyps) ue pf oty in
    EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) ff

  with EcUnify.UninstanciateUni ->
    EcTyping.tyerror pf.EcLocation.pl_loc
      (LDecl.toenv hyps) EcTyping.FreeTypeVariables

let process_form ?mv hyps pf ty =
  process_form_opt ?mv hyps pf (Some ty)

let process_formula ?mv hyps pf =
  process_form hyps ?mv pf tbool

let process_exp hyps mode oty e =
  let env = LDecl.toenv hyps in
  let ue  = unienv_of_hyps hyps in
  let e   =  EcTyping.transexpcast_opt env mode ue oty e in
    EcTypes.e_uni (EcUnify.UniEnv.close ue) e

let process_pattern hyps fp =
  let ps = ref Mid.empty in
  let ue = unienv_of_hyps hyps in
  let fp = EcTyping.trans_pattern (LDecl.toenv hyps) ps ue fp in
  ((!ps, ue), fp)

(* ------------------------------------------------------------------ *)
let pf_process_form_opt pe ?mv hyps oty pf =
  Exn.recast_pe pe hyps (fun () -> process_form_opt ?mv hyps pf oty)

let pf_process_form pe ?mv hyps ty pf =
  Exn.recast_pe pe hyps (fun () -> process_form ?mv hyps pf ty)

let pf_process_formula pe ?mv hyps pf =
  Exn.recast_pe pe hyps (fun () -> process_formula ?mv hyps pf)

let pf_process_exp pe hyps mode oty e =
  Exn.recast_pe pe hyps (fun () -> process_exp hyps mode oty e)

let pf_process_pattern pe hyps fp =
  Exn.recast_pe pe hyps (fun () -> process_pattern hyps fp)

(* ------------------------------------------------------------------ *)
let tc1_process_form_opt ?mv tc oty pf =
  Exn.recast_tc1 tc (fun hyps -> process_form_opt ?mv hyps pf oty)

let tc1_process_form ?mv tc ty pf =
  Exn.recast_tc1 tc (fun hyps -> process_form ?mv hyps pf ty)

let tc1_process_formula ?mv tc pf =
  Exn.recast_tc1 tc (fun hyps -> process_formula ?mv hyps pf)

let tc1_process_exp tc mode oty e =
  Exn.recast_tc1 tc (fun hyps -> process_exp hyps mode oty e)

let tc1_process_pattern tc fp =
  Exn.recast_tc1 tc (fun hyps -> process_pattern hyps fp)

(* ------------------------------------------------------------------ *)
let tc1_process_prhl_form_opt tc oty pf =
  let hyps, concl = FApi.tc1_flat tc in
  let ml, mr, (pr, po) =
    match concl.f_node with
    | FequivS es -> (es.es_ml, es.es_mr, (es.es_pr, es.es_po))
    | _ -> assert false
  in

  let hyps = LDecl.push_all [ml; mr] hyps in
  let mv = Msym.of_list [("pre", pr); ("post", po)] in
  pf_process_form_opt ~mv !!tc hyps oty pf

let tc1_process_prhl_form tc ty pf = tc1_process_prhl_form_opt tc (Some ty) pf

(* ------------------------------------------------------------------ *)
let tc1_process_prhl_formula tc pf =
  tc1_process_prhl_form tc tbool pf

(* ------------------------------------------------------------------ *)
let tc1_process_stmt  ?map tc mt c =
  let hyps = FApi.tc1_hyps tc in
  let hyps = LDecl.push_active (mhr,mt) hyps in
  let env  = LDecl.toenv hyps in
  let ue   = unienv_of_hyps hyps in
  let c    = Exn.recast_pe !!tc hyps (fun () -> EcTyping.transstmt ?map env ue c) in
  let esub = Exn.recast_pe !!tc hyps (fun () -> Tuni.offun (EcUnify.UniEnv.close ue)) in
  let esub = { e_subst_id with es_ty = esub; } in
  EcModules.s_subst esub c


let tc1_process_prhl_stmt ?map tc side c =
  let concl = FApi.tc1_goal tc in
  let es = match concl.f_node with FequivS es -> es | _ -> assert false in
  let mt   = snd (match side with `Left -> es.es_ml | `Right -> es.es_mr) in
  tc1_process_stmt tc mt ?map c

(* ------------------------------------------------------------------ *)
let tc1_process_Xhl_exp tc side ty e =
  let hyps, concl = FApi.tc1_flat tc in
  let m = fst (EcFol.destr_programS side concl) in

  let hyps = LDecl.push_active m hyps in
  pf_process_exp !!tc hyps `InProc ty e

(* ------------------------------------------------------------------ *)
let tc1_process_Xhl_form ?side tc ty pf =
  let hyps, concl = FApi.tc1_flat tc in

  let memory, mv =
    match concl.f_node, side with
    | FhoareS   hs, None        -> (hs.hs_m , Some (hs.hs_pr , hs.hs_po ))
    | FbdHoareS hs, None        -> (hs.bhs_m, Some (hs.bhs_pr, hs.bhs_po))
    | FequivS   es, Some `Left  -> ((mhr, snd es.es_ml), None)
    | FequivS   es, Some `Right -> ((mhr, snd es.es_mr), None)

    | _, _ -> raise (DestrError "destr_programS")
  in

  let hyps = LDecl.push_active memory hyps in
  let mv = mv |> omap
   (fun (pr, po) -> Msym.of_list [("pre", pr); ("post", po)]) in

  pf_process_form ?mv !!tc hyps ty pf

(* ------------------------------------------------------------------ *)
let tc1_process_Xhl_formula ?side tc pf =
  tc1_process_Xhl_form ?side tc tbool pf

(* ------------------------------------------------------------------ *)
(* FIXME: factor out to typing module                                 *)
(* FIXME: TC HOOK - check parameter constraints                       *)
(* ------------------------------------------------------------------ *)
let pf_check_tvi (pe : proofenv) typ tvi =
  match tvi with
  | None -> ()

  | Some (EcUnify.TVIunamed tyargs) ->
      if List.length tyargs <> List.length typ then
        tc_error pe
          "wrong number of type parameters (%d, expecting %d)"
          (List.length tyargs) (List.length typ)

  | Some (EcUnify.TVInamed tyargs) ->
      let typnames = List.map (EcIdent.name |- fst) typ in
      List.iter
        (fun (x, _) ->
          if not (List.mem x typnames) then
            tc_error pe "unknown type variable: %s" x)
        tyargs

(* -------------------------------------------------------------------- *)
exception NoMatch

type lazyred = [`Full | `NoDelta | `None]

let t_lazy_match ?(reduce = `Full) (tx : form -> FApi.backward) (tc : tcenv1) =
  let hyps, concl = FApi.tc1_flat tc in

  let rec do1 fp =
    try  tx fp tc
    with
    | NoMatch -> begin
        let strategy =
          match reduce with
          | `None    -> raise InvalidGoalShape
          | `Full    -> EcReduction.full_red
          | `NoDelta -> EcReduction.nodelta in

        match EcReduction.h_red_opt strategy hyps fp with
        | None    -> raise InvalidGoalShape
        | Some fp -> do1 fp
    end

  in do1 concl

(* -------------------------------------------------------------------- *)
let rec lazy_destruct ?(reduce = true) hyps tx fp =
  try  Some (tx fp)
  with
  | NoMatch when not reduce -> None
  | NoMatch ->
      match EcReduction.h_red_opt EcReduction.full_red hyps fp with
      | None    -> None
      | Some fp -> lazy_destruct ~reduce hyps tx fp

(* -------------------------------------------------------------------- *)
type dproduct = [
  | `Imp    of form * form
  | `Forall of EcIdent.t * gty * form
]

let destruct_product ?(reduce = true) hyps fp : dproduct option =
  let doit fp =
    match EcFol.sform_of_form fp with
    | SFquant (Lforall, (x, t), lazy f) -> `Forall (x, t, f)
    | SFimp (f1, f2) -> `Imp (f1, f2)
    | _ -> raise NoMatch
  in
    lazy_destruct ~reduce hyps doit fp

(* -------------------------------------------------------------------- *)
type dexists = [
  | `Exists of EcIdent.t * gty * form
]

let destruct_exists ?(reduce = true) hyps fp : dexists option =
  let doit fp =
    match EcFol.sform_of_form fp with
    | SFquant (Lexists, (x, t), lazy f) -> `Exists (x, t, f)
    | _ -> raise NoMatch
  in
    lazy_destruct ~reduce hyps doit fp
