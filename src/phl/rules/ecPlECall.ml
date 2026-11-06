(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcFol
open EcEnv

open EcCoreGoal

module L   = EcLocation
module APT = EcParsetree
module PT  = EcProofTerm

(* -------------------------------------------------------------------- *)
type call = EcModules.lvalue option * EcPath.xpath * EcTypes.expr list

type calls = [
  | `Single of call
  | `Double of call * call
]

(* -------------------------------------------------------------------- *)
let process_contract
  (pe    : proofenv)
  (penv  : LDecl.hyps)
  (hyps  : LDecl.hyps)
  ((ctt_path, ctt_tvi, ctt_args) : APT.pecall)
=
  let ptenv = PT.ptenv_of_penv penv pe in
  let contract = PT.process_pterm ptenv (APT.FPNamed (ctt_path, ctt_tvi)) in
  let contract, _ = PT.process_pterm_args_app contract ctt_args in
  let contract = PT.apply_pterm_to_max_holes hyps contract in
  assert (PT.can_concretize contract.PT.ptev_env);
  PT.concretize contract

(* -------------------------------------------------------------------- *)
let check_contract_type
  ?(loc      : L.t option)
  ?(phoare   : bool = false)
  ?(noexn    : bool = true)
  ~(name     : EcSymbols.qsymbol)
   (pe       : proofenv)
   (hyps     : LDecl.hyps)
   (calls    : calls)
   (contract : form)
=
  let env = LDecl.toenv hyps in

  let contract =
    EcReduction.h_red_opt EcReduction.full_red hyps contract
    |> odfl contract in

  match calls with
  | `Single (_, funname, _) -> begin
    let cttfname =
      match contract.f_node with
      | FhoareF hf ->
        if noexn then begin
          if not (POE.is_empty (hf_po hf).hsi_inv) then
            tc_error ?loc pe
              "contract must have an empty exception post-condition";
          end;
        hf.hf_f
      | FbdHoareF hf when phoare -> hf.bhf_f
      | _ ->
        tc_error_lazy ?loc pe (fun fmt ->
          Format.fprintf fmt
            "contract %a should be a Hoare statement"
            EcSymbols.pp_qsymbol name
        )
    in
    if not (EcReduction.EqTest.for_xp env funname cttfname) then begin
      tc_error_lazy ?loc pe (fun fmt ->
        let ppe = EcPrinting.PPEnv.ofenv env in
        Format.fprintf fmt
          "contract %a should be for the procedure %a, not %a"
          EcSymbols.pp_qsymbol name
          (EcPrinting.pp_funname ppe) funname
          (EcPrinting.pp_funname ppe) cttfname
      )
    end;
  end

  | `Double ((_, fl, _), (_, fr, _)) ->
    let contract =
      try
        destr_equivF contract
      with DestrError _ ->
        tc_error_lazy ?loc pe (fun fmt ->
          Format.fprintf fmt
            "contract %a should be an Equiv statement"
            EcSymbols.pp_qsymbol name
        )
    in
    List.iter (fun (f, ef_f, side) ->
      if not (EcReduction.EqTest.for_xp env f ef_f) then begin
        tc_error_lazy ?loc pe (fun fmt ->
          let ppe = EcPrinting.PPEnv.ofenv env in
          Format.fprintf fmt
            "%s-side of contract %a should be for the procedure %a, not %a"
            side
            EcSymbols.pp_qsymbol name
            (EcPrinting.pp_funname ppe) f
            (EcPrinting.pp_funname ppe) ef_f
        )
      end
    ) [(fl, contract.ef_fl, "left"); (fr, contract.ef_fr, "right")]

(* -------------------------------------------------------------------- *)
let abstract_pvs
  (hyps : LDecl.hyps)
  (ms   : memory list)
  (pvs  : ((prog_var * ty) list) EcIdent.Mid.t)
=
  let env = LDecl.toenv hyps in

  let for_memory ((subst, hyps) : EcPV.PVM.subst * LDecl.hyps) (m : memory) =
    let pvs = EcIdent.Mid.find_def [] m pvs in

    let ids = List.map (fun (pv, ty) ->
      (Format.sprintf "%s_" (EcTypes.symbol_of_pv pv)), ty) pvs in
    let fresh = LDecl.fresh_ids hyps (List.fst ids) in
    let hyps =
      List.fold_left2 (fun hyps id (_, ty) ->
        LDecl.add_local id (LD_var (ty, None)) hyps)
        hyps fresh ids in
    let ids = List.combine fresh (List.snd ids) in

    let pvfs = List.map (fun (pv, ty) -> (f_pvar pv ty m).inv) pvs in
    let subst = List.fold_left (fun subst ((pv, ty), x) ->
      EcPV.PVM.add env pv m (f_local x ty) subst
    ) subst (List.combine pvs (List.fst ids)) in

    ((subst, hyps), (ids, pvfs))
  in

  let (subst, _), ids =
    List.fold_left_map for_memory (EcPV.PVM.empty, hyps) ms in

  let pvfs = List.flatten (List.snd ids) in
  let ids  = List.flatten (List.fst ids) in

  ids, pvfs, subst

(* -------------------------------------------------------------------- *)
let restore_pvs (ids : (EcIdent.t * ty) list) (pvfs : form list) =
  List.fold_left2
    (fun s (id, _) pv -> EcSubst.add_flocal s id pv)
    EcSubst.empty ids pvfs

(* -------------------------------------------------------------------- *)
let subst_pt_args (env : env) (subst : EcPV.PVM.subst) (pt : proofterm) =
  match pt with
  | PTApply { pt_head; pt_args } ->
      let pt_args = List.map (PT.subst_pv_pt_arg env subst) pt_args in
      PTApply { pt_head; pt_args }
  | _ -> assert false
