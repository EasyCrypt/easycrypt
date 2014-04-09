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
let ptenv pe hyps (ue, ev) =
  { pte_pe = pe;
    pte_hy = hyps;
    pte_ue = EcUnify.UniEnv.copy ue;
    pte_ev = ref ev; }

(* -------------------------------------------------------------------- *)
let copy pe =
  ptenv pe.pte_pe pe.pte_hy (pe.pte_ue, !(pe.pte_ev))

(* -------------------------------------------------------------------- *)
let ptenv_of_penv (hyps : LDecl.hyps) (pe : proofenv) =
  { pte_pe = pe;
    pte_hy = hyps;
    pte_ue = EcProofTyping.unienv_of_hyps hyps;
    pte_ev = ref EcMatching.EV.empty; }

(* -------------------------------------------------------------------- *)
let can_concretize (pt : pt_env) =
     EcUnify.UniEnv.closed pt.pte_ue
  && EcMatching.EV.filled  !(pt.pte_ev)

(* -------------------------------------------------------------------- *)
type cptenv = CPTEnv of f_subst

(* -------------------------------------------------------------------- *)
let concretize_env pe =
(*  assert (can_concretize pe); *)

  let tysubst  = { ty_subst_id with ts_u = EcUnify.UniEnv.close pe.pte_ue } in
  let ftysubst = Fsubst.f_subst_init false Mid.empty tysubst EcPath.Mp.empty in
  let subst   =
    EcMatching.EV.fold
      (fun x f s ->
         let f = Fsubst.f_subst ftysubst f in
           Fsubst.f_bind_local s x f)
      !(pe.pte_ev)
      (Fsubst.f_subst_init false Mid.empty tysubst EcPath.Mp.empty)
  in
    CPTEnv subst

(* -------------------------------------------------------------------- *)
let concretize_e_form (CPTEnv subst) f =
  Fsubst.f_subst subst f

(* -------------------------------------------------------------------- *)
let rec concretize_e_arg ((CPTEnv subst) as cptenv) arg =
  match arg with
  | PAFormula f        -> PAFormula (Fsubst.f_subst subst f)
  | PAMemory  m        -> PAMemory m
  | PAModule  (mp, ms) -> PAModule (mp, ms)
  | PASub     pt       -> PASub (pt |> omap (concretize_e_pt cptenv))


and concretize_e_head (CPTEnv subst) head =
  match head with
  | PTCut    f        -> PTCut    (Fsubst.f_subst subst f)
  | PTHandle h        -> PTHandle h
  | PTLocal  x        -> PTLocal  x
  | PTGlobal (p, tys) -> PTGlobal (p, List.map subst.fs_ty tys)

and concretize_e_pt cptenv { pt_head; pt_args } =
  { pt_head = concretize_e_head cptenv pt_head;
    pt_args = List.map (concretize_e_arg cptenv) pt_args; }

(* -------------------------------------------------------------------- *)
let concretize_form pe f =
  concretize_e_form (concretize_env pe) f

(* -------------------------------------------------------------------- *)
let rec concretize ({ ptev_env = pe } as pt) =
  let (CPTEnv subst) as cptenv = concretize_env pe in
  (concretize_e_pt cptenv pt.ptev_pt, Fsubst.f_subst subst pt.ptev_ax)

(* -------------------------------------------------------------------- *)
let pt_of_hyp pf hyps x =
  let ptenv = ptenv_of_penv hyps pf in
  let ax    = LDecl.lookup_hyp_by_id x hyps in

  { ptev_env = ptenv;
    ptev_pt  = { pt_head = PTLocal x; pt_args = []; };
    ptev_ax  = ax; }

(* -------------------------------------------------------------------- *)
let pt_of_global pf hyps p tys =
  let ptenv = ptenv_of_penv hyps pf in
  let ax    = EcEnv.Ax.instanciate p tys (LDecl.toenv hyps) in

  { ptev_env = ptenv;
    ptev_pt  = { pt_head = PTGlobal (p, tys); pt_args = []; };
    ptev_ax  = ax; }

(* -------------------------------------------------------------------- *)
let pattern_form ?name hyps ~ptn subject =
  let dfl () = Printf.sprintf "x%d" (EcUid.unique ()) in

  let x    = EcIdent.create (ofdfl dfl name) in
  let fx   = EcFol.f_local x ptn.f_ty in
  let body =
    Hf.memo_rec 107
      (fun aux f ->
        if   EcReduction.is_alpha_eq hyps f ptn
        then fx
        else f_map (fun ty -> ty) aux f)
      subject
  in (x, body)

(* -------------------------------------------------------------------- *)
let pf_form_match (pt : pt_env) ?mode ~ptn subject =
  let mode = mode |> odfl EcMatching.fmrigid in

  try
    let (ue, ev) =
      EcMatching.f_match_core mode pt.pte_hy
        (pt.pte_ue, !(pt.pte_ev)) ~ptn subject
    in
      EcUnify.UniEnv.restore ~dst:pt.pte_ue ~src:ue;
      pt.pte_ev := ev
  with EcMatching.MatchFailure as exn ->
    (* FIXME: should we check for empty inters. with ecmap? *)
    if not (EcReduction.is_conv pt.pte_hy ptn subject) then
      raise exn

(* -------------------------------------------------------------------- *)
let pf_find_occurence (pt : pt_env) ~ptn subject =
  let module E = struct exception MatchFound end in

  let na = List.length (snd (EcFol.destr_app ptn)) in

  let trymatch bds _pos tp =
    let tp =
      match tp.f_node with
      | Fapp (h, hargs) when List.length hargs > na ->
          let (a1, a2) = List.take_n na hargs in
            f_app h a1 (toarrow (List.map f_ty a2) tp.f_ty)
      | _ -> tp
    in

    try
      if not (Mid.set_disjoint bds tp.f_fv) then
        `Continue
      else begin
        pf_form_match pt ~ptn tp;
        raise E.MatchFound
      end
    with EcMatching.MatchFailure -> `Continue
  in

  try
    ignore (EcMatching.FPosition.select trymatch subject);
    raise EcMatching.MatchFailure
  with E.MatchFound -> ()

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
(* Try to extract a ffpattern parse-tree from a genpattern parse-tree.
 * This allows to mix proof-terms and formulas/values in tactic
 * arguments. Priority should always been given to ffpattern as it is
 * always possible to force the interpretation of a genpattern as a
 * formula with holes by annotating it with an empty {} occurences
 * selector *)

let ffpattern_of_genpattern hyps (ge : genpattern) =
  match ge with
  | `FPattern pe      -> Some pe
  | `Form (Some _, _) -> None
  | `Form (None, fp)  ->
      let rec destr_app fp =
        match unloc fp with
        | PFtuple [fp] -> destr_app fp
        | PFapp (fh, fargs) -> (fh, fargs)
        | _ -> (fp, [])

      and ae_of_form fp =
        match unloc fp with
        | PFhole -> mk_loc fp.pl_loc EA_none
        | _      -> mk_loc fp.pl_loc (EA_form fp)
      in
        match destr_app fp with
        | ({ pl_desc = PFident (p, tya) }, args) ->
            let hastyp = not (EcUtils.is_none tya) in
            if lookup_named_psymbol hyps ~hastyp (unloc p) <> None then
              Some ({ fp_kind = FPNamed (p, tya);
                      fp_args = List.map ae_of_form args; })
            else
              None

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

  EcProofTyping.pf_check_tvi pe.pte_pe typ tvi;

  (* FIXME: TC HOOK *)
  let fs  = EcUnify.UniEnv.opentvi pe.pte_ue typ tvi in
  let ax  = Fsubst.subst_tvar fs ax in
  let typ = List.map (fun (a, _) -> EcIdent.Mid.find a fs) typ in

  (p, (typ, ax))

(* ------------------------------------------------------------------ *)
let process_pterm_cut ~prcut pe pt =
  let (pt, ax) =
    match pt with
    | FPNamed (fp, tyargs) -> begin
        match process_named_pterm pe (tyargs, fp) with
        | (`Local  x, ([] , ax)) -> (PTLocal  x, ax)
        | (`Global p, (typ, ax)) -> (PTGlobal (p, typ), ax)

        | _ -> assert false
    end

  | FPCut fp -> let fp = prcut fp in (PTCut fp, fp)
  in

  let pt = { pt_head = pt; pt_args = []; } in

  { ptev_env = pe; ptev_pt = pt; ptev_ax = ax; }

(* ------------------------------------------------------------------ *)
let process_pterm pe pt =
  let prcut = EcProofTyping.pf_process_formula pe.pte_pe pe.pte_hy in
  process_pterm_cut prcut pe pt

(* ------------------------------------------------------------------ *)
let trans_pterm_arg_impl pe f =
  let pt = { pt_head = PTCut f; pt_args = []; } in
  let pt = { ptev_env = pe; ptev_pt = pt; ptev_ax = f; } in
    { ptea_env = pe; ptea_arg = PVASub pt; }

(* ------------------------------------------------------------------ *)
let trans_pterm_arg_value pe ?name { pl_desc = arg } =
  let dfl () = Printf.sprintf "x%d" (EcUid.unique ()) in

  match arg with
  | EA_mod _ | EA_mem _ -> tc_pterm_apperror pe.pte_pe `FormWanted

  | EA_none ->
      let aty = EcUnify.UniEnv.fresh pe.pte_ue in
      let x   = EcIdent.create (ofdfl dfl name) in
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
  match EcProofTyping.destruct_product pe.pte_hy pt.ptev_ax with
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
let dfl_arg_for_impl  pe f arg = ofdfl (fun () -> (hole_for_impl  pe f).ptea_arg) arg
let dfl_arg_for_mem   pe   arg = ofdfl (fun () -> (hole_for_mem   pe  ).ptea_arg) arg
let dfl_arg_for_mod   pe   arg = ofdfl (fun () -> (hole_for_mod   pe  ).ptea_arg) arg
let dfl_arg_for_value pe   arg = ofdfl (fun () -> (hole_for_value pe  ).ptea_arg) arg

(* -------------------------------------------------------------------- *)
let check_pterm_oarg pe (x, xty) f arg =
  let env = LDecl.toenv (pe.pte_hy) in

  match xty with
  | GTty xty -> begin
      match dfl_arg_for_value pe arg with
      | PVAFormula arg -> begin
        try
          pf_unify pe xty arg.f_ty;
          (Fsubst.f_subst_local x arg f, PAFormula arg)
        with EcUnify.UnificationFailure _ ->
          tc_pterm_apperror pe.pte_pe `InvalidArgForm
      end
      | _ -> tc_pterm_apperror pe.pte_pe `FormWanted
  end

  | GTmem _ -> begin
      match dfl_arg_for_mem pe arg with
      | PVAMemory arg -> (Fsubst.f_subst_mem x arg f, PAMemory arg)
      | _ -> tc_pterm_apperror pe.pte_pe `MemoryWanted
  end

  | GTmodty (emt, restr) -> begin
      match dfl_arg_for_mod pe arg with
      | PVAModule (mp, mt) ->
          EcTyping.check_modtype_with_restrictions env mp mt emt restr;
          EcPV.check_module_in env mp emt;
          (Fsubst.f_subst_mod x mp f, PAModule (mp, mt))
      | _ -> tc_pterm_apperror pe.pte_pe `ModuleWanted
  end

(* -------------------------------------------------------------------- *)
let check_pterm_arg pe (x, xty) f arg =
  check_pterm_oarg pe (x, xty) f (Some arg)

(* -------------------------------------------------------------------- *)
let apply_pterm_to_oarg ({ ptev_env = pe; ptev_pt = rawpt; } as pt) oarg =
  assert (odfl true (oarg |> omap (fun arg -> pe == arg.ptea_env)));

  let oarg = oarg |> omap (fun arg -> arg.ptea_arg) in

  match EcProofTyping.destruct_product pe.pte_hy pt.ptev_ax with
  | None   -> tc_pterm_apperror pe.pte_pe `NotFunctional
  | Some t ->
      let (newax, newarg) =
        match t with
        | `Imp (f1, f2) -> begin
            match dfl_arg_for_impl pe f1 oarg with
            | PVASub arg -> begin
              try
                pf_form_match pe ~ptn:arg.ptev_ax f1;
                (f2, PASub (Some arg.ptev_pt))
              with EcMatching.MatchFailure ->
                tc_pterm_apperror pe.pte_pe `InvalidArgProof
            end
            | _ -> tc_pterm_apperror pe.pte_pe `PTermWanted
        end

        | `Forall (x, xty, f) ->
             check_pterm_oarg pe (x, xty) f oarg
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
let process_full_pterm_cut ~prcut pe pf =
  let pt = process_pterm_cut ~prcut pe pf.fp_kind in
    process_pterm_args_app pt pf.fp_args

(* -------------------------------------------------------------------- *)
let process_full_pterm pe pf =
  let pt = process_pterm pe pf.fp_kind in
    process_pterm_args_app pt pf.fp_args

(* -------------------------------------------------------------------- *)
let process_full_closed_pterm_cut ~prcut pe pf =
  let pt = process_pterm_cut ~prcut pe pf.fp_kind in
  let pt = process_pterm_args_app pt pf.fp_args in
    (* FIXME: use core exception? *)
    if not (can_concretize pe) then
      tc_error pe.pte_pe "cannot infer all placeholders";
    concretize pt

(* -------------------------------------------------------------------- *)
let process_full_closed_pterm pe pf =
  let pt = process_pterm pe pf.fp_kind in
  let pt = process_pterm_args_app pt pf.fp_args in
    (* FIXME: use core exception? *)
    if not (can_concretize pe) then
      tc_error pe.pte_pe "cannot infer all placeholders";
    concretize pt

(* -------------------------------------------------------------------- *)
let tc1_process_pterm_cut ~prcut tc ff =
  let pe   = FApi.tc1_penv tc in
  let hyps = FApi.tc1_hyps tc in
  process_pterm_cut ~prcut (ptenv_of_penv hyps pe) ff

(* -------------------------------------------------------------------- *)
let tc1_process_pterm tc ff =
  let pe   = FApi.tc1_penv tc in
  let hyps = FApi.tc1_hyps tc in
  process_pterm (ptenv_of_penv hyps pe) ff

(* -------------------------------------------------------------------- *)
let tc1_process_full_pterm_cut ~prcut (tc : tcenv1) (ff : 'a fpattern) =
  let pe   = FApi.tc1_penv tc in
  let hyps = FApi.tc1_hyps tc in
  process_full_pterm_cut ~prcut (ptenv_of_penv hyps pe) ff

(* -------------------------------------------------------------------- *)
let tc1_process_full_pterm (tc : tcenv1) (ff : ffpattern) =
  let pe   = FApi.tc1_penv tc in
  let hyps = FApi.tc1_hyps tc in
  process_full_pterm (ptenv_of_penv hyps pe) ff

(* -------------------------------------------------------------------- *)
let tc1_process_full_closed_pterm_cut ~prcut (tc : tcenv1) (ff : 'a fpattern) =
  let pe   = FApi.tc1_penv tc in
  let hyps = FApi.tc1_hyps tc in
  process_full_closed_pterm_cut ~prcut (ptenv_of_penv hyps pe) ff

(* -------------------------------------------------------------------- *)
let tc1_process_full_closed_pterm (tc : tcenv1) (ff : ffpattern) =
  let pe   = FApi.tc1_penv tc in
  let hyps = FApi.tc1_hyps tc in
  process_full_closed_pterm (ptenv_of_penv hyps pe) ff
