(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcTypes
open EcFol
open EcEnv
open EcCoreGoal
open EcAst
open EcParsetree

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
    let ts = Tuni.subst (EcUnify.UniEnv.close ue) in
    EcFol.Fsubst.f_subst ts ff

  with EcUnify.UninstanciateUni ->
    EcTyping.tyerror pf.EcLocation.pl_loc
      (LDecl.toenv hyps) EcTyping.FreeTypeVariables

let process_form ?mv hyps pf ty =
  process_form_opt ?mv hyps pf (Some ty)

let process_formula ?mv hyps pf =
  process_form hyps ?mv pf tbool

let process_xreal ?mv hyps pf =
  process_form hyps ?mv pf txreal

let process_dformula ?mv hyps pf =
  match pf with
  | Single pf -> Single(process_formula ?mv hyps pf)
  | Double(pp,pf) ->
    let p = process_formula ?mv hyps pp in
    let f = process_xreal ?mv hyps pf in
    Double(p,f)

let process_exp hyps mode oty e =
  let env = LDecl.toenv hyps in
  let ue  = unienv_of_hyps hyps in
  let e   = EcTyping.transexpcast_opt env mode ue oty e in
  let ts  = Tuni.subst (EcUnify.UniEnv.close ue)  in
  e_subst ts e

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

let pf_process_xreal pe ?mv hyps pf =
  Exn.recast_pe pe hyps (fun () -> process_xreal ?mv hyps pf)

let pf_process_dformula pe ?mv hyps pf =
  Exn.recast_pe pe hyps (fun () -> process_dformula ?mv hyps pf)

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
    | FequivS es -> (es.es_ml, es.es_mr, (es_pr es, es_po es))
    | _ -> assert false
  in

  let hyps = LDecl.push_active_ts ml mr hyps in
  let mv = Msym.of_list [("pre", pr.inv); ("post", po.inv)] in
  let f = pf_process_form_opt ~mv !!tc hyps oty pf in
  let ml, mr = fst ml, fst mr in
  {ml;mr;inv=f}

let tc1_process_prhl_form tc ty pf = tc1_process_prhl_form_opt tc (Some ty) pf

(* ------------------------------------------------------------------ *)
let tc1_process_prhl_formula tc pf =
  tc1_process_prhl_form tc tbool pf

(* ------------------------------------------------------------------ *)
let tc1_process_stmt ?map hyps tc c =
  let env    = LDecl.toenv hyps in
  let ue     = unienv_of_hyps hyps in
  let c      = Exn.recast_pe !!tc hyps (fun () -> EcTyping.transstmt ?map env ue c) in
  let uidmap = Exn.recast_pe !!tc hyps (fun () -> EcUnify.UniEnv.close ue) in
  let es     = Tuni.subst uidmap in
  s_subst es c


let tc1_process_prhl_stmt ?map tc side c =
  let concl = FApi.tc1_goal tc in
  let ml, mr = match concl.f_node with 
    | FequivS {es_ml=ml; es_mr=mr} -> (ml, mr)
    | FeagerF {eg_ml=ml; eg_mr=mr} ->
        EcMemory.abstract ml, EcMemory.abstract mr
    | _ -> assert false in
  let hyps   = FApi.tc1_hyps tc in
  let hyps   = LDecl.push_active_ts ml mr hyps in
  let hyps = LDecl.push_active_ss (sideif side ml mr) hyps in
  tc1_process_stmt hyps tc ?map c

let tc1_process_Xhl_stmt ?map tc c =
  let concl = FApi.tc1_goal tc in
  let m = match concl.f_node with FbdHoareS {bhs_m=m} | FhoareS {hs_m=m} -> m | _ -> assert false in
  let hyps   = FApi.tc1_hyps tc in
  let hyps   = LDecl.push_active_ss m hyps in
  tc1_process_stmt hyps tc ?map c

(* ------------------------------------------------------------------ *)
let tc1_process_Xhl_exp tc side ty e =
  let hyps, concl = FApi.tc1_flat tc in
  let m = fst (EcFol.destr_programS side concl) in

  let hyps = LDecl.push_active_ss m hyps in
  pf_process_exp !!tc hyps `InProc ty e

(* ------------------------------------------------------------------ *)
let tc1_process_Xhl_form ?side tc ty pf =
  let hyps, concl = FApi.tc1_flat tc in
  let m = fst (EcFol.destr_programS side concl) in

  let mv =
    match concl.f_node with
    | FhoareS   hs -> Some ((hs_pr hs).inv , (hs_po hs).inv )
    | FeHoareS  hs -> Some ((ehs_pr hs).inv, (ehs_po hs).inv)
    | FbdHoareS hs -> Some ((bhs_pr hs).inv, (bhs_po hs).inv)
    | _            -> None
  in

  let hyps = LDecl.push_active_ss m hyps in

  let mv =
    Option.map
      (fun (pr, po) -> Msym.of_list [("pre", pr); ("post", po)])
      mv
  in

  (snd m, {m=fst m;inv=pf_process_form ?mv !!tc hyps ty pf})

(* ------------------------------------------------------------------ *)
let tc1_process_Xhl_formula ?side tc pf =
  tc1_process_Xhl_form ?side tc tbool pf

(* ------------------------------------------------------------------ *)
let tc1_process_Xhl_formula_xreal tc pf =
  tc1_process_Xhl_form tc txreal pf

(* ------------------------------------------------------------------ *)
let tc1_process_codepos_range tc (side, cpr) =
  let me, _ = EcLowPhlGoal.tc1_get_stmt side tc in
  let env = FApi.tc1_env tc in
  let env = EcEnv.Memory.push_active_ss me env in
  EcTyping.trans_codepos_range env cpr

(* ------------------------------------------------------------------ *)
let tc1_process_codepos tc (side, cpos) =
  let me, _ = EcLowPhlGoal.tc1_get_stmt side tc in
  let env = FApi.tc1_env tc in
  let env = EcEnv.Memory.push_active_ss me env in
  EcTyping.trans_codepos env cpos

(* ------------------------------------------------------------------ *)
let tc1_process_codepos1 tc (side, cpos) =
  let me, _ = EcLowPhlGoal.tc1_get_stmt side tc in
  let env = FApi.tc1_env tc in
  let env = EcEnv.Memory.push_active_ss me env in
  EcTyping.trans_codepos1 env cpos

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
