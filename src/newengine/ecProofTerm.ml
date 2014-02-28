(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcParsetree
open EcIdent
open EcTypes
open EcFol
open EcEnv
open EcCoreGoal

module L = EcLocation

(* -------------------------------------------------------------------- *)
type evmap = form EcMatching.evmap

type pt_env = {
  pte_pe : proofenv;
  pte_hy : LDecl.hyps;
  pte_ue : EcUnify.unienv;
  pte_ev : evmap ref;
}

type pt_ev = {
  ptev_env : pt_env;
  ptev_pt  : proofterm;
  ptev_ax  : form;
}

type pt_ev_arg = {
  ptea_env : pt_env;
  ptea_arg : pt_ev_arg_r;
}

and pt_ev_arg_r =
| PVAFormula of EcFol.form
| PVAMemory  of EcMemory.memory
| PVAModule  of (EcPath.mpath * EcModules.module_sig)
| PVASub     of pt_ev

(* -------------------------------------------------------------------- *)
let tc_pterm_apperror _pe ?loc _kind =
  ignore loc;
  assert false

(* -------------------------------------------------------------------- *)
let ptenv_of_tcenv (tc : tcenv) =
  { pte_pe = FApi.tc_penv tc;
    pte_hy = FApi.tc_hyps tc;
    pte_ue = Typing.unienv_of_hyps (FApi.tc_hyps tc);
    pte_ev = ref EcMatching.EV.empty; }

(* -------------------------------------------------------------------- *)
let pf_form_match (pt : pt_env) ~ptn subject =
  try
    let (ue, ev) =
      EcMatching.f_match_core EcMatching.fmrigid pt.pte_hy
        (pt.pte_ue, !(pt.pte_ev)) ~ptn subject
    in
      EcUnify.UniEnv.restore ~dst:pt.pte_ue ~src:ue;
      pt.pte_ev := ev
  with EcMatching.MatchFailure as exn ->
    (* FIXME: should we check for empty inters. with ecmap? *)
    if not (EcReduction.is_conv pt.pte_hy ptn subject) then
      raise exn

(* -------------------------------------------------------------------- *)
let pf_unify (pt : pt_env) ty1 ty2 =
  let ue = EcUnify.UniEnv.copy pt.pte_ue in
    EcUnify.unify (LDecl.toenv pt.pte_hy) ue ty1 ty2;
    EcUnify.UniEnv.restore ~dst:pt.pte_ue ~src:ue

(* -------------------------------------------------------------------- *)
let rec pmsymbol_of_pform fp : pmsymbol option =
  match unloc fp with
  | PFident ({ pl_desc = (nm, x); pl_loc = loc }, _) when EcIo.is_mod_ident x ->
      Some (List.map (fun nm1 -> (mk_loc loc nm1, None)) (nm @ [x]))

  | PFapp ({ pl_desc = PFident ({ pl_desc = (nm, x); pl_loc = loc }, _) },
           [{ pl_desc = PFtuple args; }]) -> begin

    let mod_ = List.map (fun nm1 -> (mk_loc loc nm1, None)) nm in
    let args =
      List.map
        (fun a -> pmsymbol_of_pform a |> omap (mk_loc a.pl_loc))
        args
    in

      match List.exists (fun x -> x = None) args with
      | true  -> None
      | false ->
          let args = List.map (fun a -> oget a) args in
            Some (mod_ @ [mk_loc loc x, Some args])
  end

  | PFtuple [fp] -> pmsymbol_of_pform fp

  | _ -> None

(* ------------------------------------------------------------------ *)
let lookup_named_psymbol (hyps : LDecl.hyps) ~hastyp fp =
  match fp with
  | ([], x) when LDecl.has_hyp x hyps && not hastyp ->
      let (x, fp) = LDecl.lookup_hyp x hyps in
        Some (`Local x, ([], fp))

  | _ ->
    match EcEnv.Ax.lookup_opt fp (LDecl.toenv hyps) with
    | Some (p, ({ EcDecl.ax_spec = Some fp } as ax)) ->
        Some (`Global p, (ax.EcDecl.ax_tparams, fp))
    | _ -> None

(* -------------------------------------------------------------------- *)
let process_named_pterm pe (tvi, fp) =
  let env = LDecl.toenv pe.pte_hy in

  let (p, (typ, ax)) =
    match lookup_named_psymbol pe.pte_hy ~hastyp:(tvi <> None) (unloc fp) with
    | Some (p, ax) -> (p, ax)
    | None -> tc_lookup_error pe.pte_pe `Lemma (unloc fp)
  in

  let tvi =
    Exn.recast_pe pe.pte_pe
      (fun () -> omap (EcTyping.transtvi env pe.pte_ue) tvi)
  in

  Typing.pf_check_tvi pe.pte_pe typ tvi;

  (* FIXME: TC HOOK *)
  let fs  = EcUnify.UniEnv.opentvi pe.pte_ue typ tvi in
  let ax  = Fsubst.subst_tvar fs ax in
  let typ = List.map (fun (a, _) -> EcIdent.Mid.find a fs) typ in

  (p, (typ, ax))

(* ------------------------------------------------------------------ *)
let process_pterm pe pt =
  let (pt, ax) =
    match pt with
    | FPNamed (fp, tyargs) -> begin
        match process_named_pterm pe (tyargs, fp) with
        | (`Local  x, ([] , ax)) -> (PTLocal  x, ax)
        | (`Global p, (typ, ax)) -> (PTGlobal (p, typ), ax)

        | _ -> assert false
    end

  | FPCut fp ->
      let fp = Typing.pf_process_formula pe.pte_pe pe.pte_hy fp in
        (PTCut fp, fp)
  in

  let pt = { pt_head = pt; pt_args = []; } in

  { ptev_env = pe; ptev_pt = pt; ptev_ax = ax; }

(* ------------------------------------------------------------------ *)
let trans_pterm_arg_impl pe f =
  let pt = { pt_head = PTCut f; pt_args = []; } in
  let pt = { ptev_env = pe; ptev_pt = pt; ptev_ax = f; } in
    { ptea_env = pe; ptea_arg = PVASub pt; }

(* ------------------------------------------------------------------ *)
let trans_pterm_arg_value pe ?name { pl_desc = arg } =
  match arg with
  | EA_mod _ | EA_mem _ -> tc_pterm_apperror pe.pte_pe `FormWanted

  | EA_none ->
      let aty = EcUnify.UniEnv.fresh pe.pte_ue in
      let x   = EcIdent.create (odfl "x" name) in
        pe.pte_ev := EcMatching.EV.add x !(pe.pte_ev);
        { ptea_env = pe; ptea_arg = PVAFormula (f_local x aty); }

  | EA_form fp ->
      let env = LDecl.toenv pe.pte_hy in
      let fp  = (fun () -> EcTyping.trans_form_opt env pe.pte_ue fp None) in
      let fp  = Exn.recast_pe pe.pte_pe fp in
        { ptea_env = pe; ptea_arg = PVAFormula fp; }

(* ------------------------------------------------------------------ *)
let trans_pterm_arg_mod pe arg =
  let mp =
    match unloc arg with
    | EA_none    -> tc_pterm_apperror pe.pte_pe `CannotInfer
    | EA_mem _   -> tc_pterm_apperror pe.pte_pe `ModuleWanted
    | EA_mod mp  -> mp
    | EA_form fp ->
      match pmsymbol_of_pform fp with
      | None    -> tc_pterm_apperror pe.pte_pe `ModuleWanted
      | Some mp -> mk_loc arg.pl_loc mp
  in

  let env  = LDecl.toenv pe.pte_hy in
  let mod_ = (fun () -> EcTyping.trans_msymbol env mp) in
  let mod_ = Exn.recast_pe pe.pte_pe mod_ in

    { ptea_env = pe; ptea_arg = PVAModule mod_; }

(* ------------------------------------------------------------------ *)
let trans_pterm_arg_mem pe { pl_desc = arg } =
  match arg with
  | EA_none -> tc_pterm_apperror pe.pte_pe `CannotInfer
  | EA_mod _ | EA_form _ -> tc_pterm_apperror pe.pte_pe `MemoryWanted

  | EA_mem mem ->
      let env = LDecl.toenv pe.pte_hy in
      let mem = Exn.recast_pe pe.pte_pe (fun () -> EcTyping.transmem env mem) in
        { ptea_env = pe; ptea_arg = PVAMemory mem; }

(* ------------------------------------------------------------------ *)
let process_pterm_arg ({ ptev_env = pe } as pt) arg =
  match EcLogic.destruct_product pe.pte_hy pt.ptev_ax with
  | None -> tc_pterm_apperror pe.pte_pe `NotFunctional

  | Some (`Imp (f, _)) -> begin
      match unloc arg with
      | EA_none -> trans_pterm_arg_impl pe f
      | _       -> tc_pterm_apperror pe.pte_pe `PTermWanted
  end

  | Some (`Forall (x, xty, _)) -> begin
      match xty with
      | GTty    _ -> trans_pterm_arg_value pe ~name:(EcIdent.name x) arg
      | GTmodty _ -> trans_pterm_arg_mod pe arg
      | GTmem   _ -> trans_pterm_arg_mem pe arg
  end

(* -------------------------------------------------------------------- *)
let hole_for_impl  pe f = trans_pterm_arg_impl  pe f
let hole_for_mem   pe   = trans_pterm_arg_mem   pe (L.mk_loc L._dummy EA_none)
let hole_for_mod   pe   = trans_pterm_arg_mod   pe (L.mk_loc L._dummy EA_none)
let hole_for_value pe   = trans_pterm_arg_value pe (L.mk_loc L._dummy EA_none)

(* -------------------------------------------------------------------- *)
let dfl_arg_for_impl  pe f arg = ofdfl (fun () -> hole_for_impl  pe f) arg
let dfl_arg_for_mem   pe   arg = ofdfl (fun () -> hole_for_mem   pe  ) arg
let dfl_arg_for_mod   pe   arg = ofdfl (fun () -> hole_for_mod   pe  ) arg
let dfl_arg_for_value pe   arg = ofdfl (fun () -> hole_for_value pe  ) arg

(* -------------------------------------------------------------------- *)
let apply_pterm_to_oarg ({ ptev_env = pe; ptev_pt = rawpt; } as pt) oarg =
  let env = LDecl.toenv pe.pte_hy in
  assert (odfl true (oarg |> omap (fun arg -> pe == arg.ptea_env)));
  match EcLogic.destruct_product pe.pte_hy pt.ptev_ax with
  | None   -> tc_pterm_apperror pe.pte_pe `NotFunctional
  | Some t ->
      let (newax, newarg) =
        match t with
        | `Imp (f1, f2) -> begin
            match (dfl_arg_for_impl pe f1 oarg).ptea_arg with
            | PVASub arg -> begin
              try
                pf_form_match pe ~ptn:arg.ptev_ax f1;
                (f2, PASub arg.ptev_pt)
              with EcMatching.MatchFailure ->
                tc_pterm_apperror pe.pte_pe `InvalidArgProof
            end
            | _ -> tc_pterm_apperror pe.pte_pe `PTermWanted
        end

        | `Forall (x, GTty xty, f) -> begin
            match (dfl_arg_for_value pe oarg).ptea_arg with
            | PVAFormula arg -> begin
              try
                pf_unify pe xty arg.f_ty;
                (Fsubst.f_subst_local x arg f, PAFormula arg)
              with EcUnify.UnificationFailure _ ->
                tc_pterm_apperror pe.pte_pe `InvalidArgForm
            end
            | _ -> tc_pterm_apperror pe.pte_pe `FormWanted
        end

        | `Forall (x, GTmem _, f) -> begin
            match (dfl_arg_for_mem pe oarg).ptea_arg with
            | PVAMemory arg -> (Fsubst.f_subst_mem x arg f, PAMemory arg)
            | _ -> tc_pterm_apperror pe.pte_pe `MemoryWanted
        end

        | `Forall (x, GTmodty (emt, restr), f) -> begin
            match (dfl_arg_for_mod pe oarg).ptea_arg with
            | PVAModule (mp, mt) ->
                (* FIXME: [check_modtype_restr/check_module_in] have awful interfaces! *)
                EcLogic.check_modtype_restr env mp mt emt restr;
                EcPV.check_module_in env mp emt;
                (Fsubst.f_subst_mod x mp f, PAModule (mp, mt))
            | _ -> tc_pterm_apperror pe.pte_pe `ModuleWanted
        end
      in

      let rawargs = rawpt.pt_args @ [newarg] in
      { pt with ptev_ax = newax; ptev_pt = { rawpt with pt_args = rawargs } }

(* -------------------------------------------------------------------- *)
let apply_pterm_to_arg pt arg =
  apply_pterm_to_oarg pt (Some arg)

(* -------------------------------------------------------------------- *)
let apply_pterm_to_hole pt =
  apply_pterm_to_oarg pt None

(* -------------------------------------------------------------------- *)
let process_pterm_arg_app pt arg =
  apply_pterm_to_arg pt (process_pterm_arg pt arg)

(* -------------------------------------------------------------------- *)
let process_pterm_args_app pt args =
  List.fold_left process_pterm_arg_app pt args

(* -------------------------------------------------------------------- *)
let process_full_pterm pe pf =
  let pt = process_pterm pe pf.fp_kind in
    process_pterm_args_app pt pf.fp_args

(* -------------------------------------------------------------------- *)
let tc_process_full_pterm (tc : tcenv) (ff : ffpattern) =
  process_full_pterm (ptenv_of_tcenv tc) ff

(* -------------------------------------------------------------------- *)
let can_concretize (pt : pt_env) =
     EcUnify.UniEnv.closed pt.pte_ue
  && EcMatching.EV.filled  !(pt.pte_ev)

(* -------------------------------------------------------------------- *)
let concretize ({ ptev_env = pe } as pt) =
  assert (can_concretize pe);

  let tysubst = { ty_subst_id with ts_u = EcUnify.UniEnv.close pe.pte_ue } in
  let subst   =
    EcMatching.EV.fold
      (fun x f s -> Fsubst.f_bind_local s x f) !(pe.pte_ev)
      (Fsubst.f_subst_init false Mid.empty tysubst EcPath.Mp.empty)
  in

  let onform f = Fsubst.f_subst subst f in

  let rec onpthead = function
    | PTCut    f        -> PTCut (onform f)
    | PTHandle h        -> PTHandle h
    | PTLocal  x        -> PTLocal  x
    | PTGlobal (p, tys) -> PTGlobal (p, List.map (ty_subst tysubst) tys)

  and onptarg = function
    | PAFormula f        -> PAFormula (onform f)
    | PAMemory  m        -> PAMemory m
    | PAModule  (mp, ms) -> PAModule (mp, ms)
    | PASub     pt       -> PASub (onpt pt)

  and onpt { pt_head; pt_args } =
    { pt_head = onpthead pt_head;
      pt_args = List.map onptarg pt_args; }

  in
    (onpt pt.ptev_pt, onform pt.ptev_ax)
