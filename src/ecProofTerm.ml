(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcParsetree
open EcIdent
open EcTypes
open EcFol
open EcEnv
open EcMatching
open EcCoreGoal

module L  = EcLocation
module PT = EcProofTyping

(* -------------------------------------------------------------------- *)
type pt_env = {
  pte_pe : proofenv;
  pte_hy : LDecl.hyps;
  pte_ue : EcUnify.unienv;
  pte_ev : EcMatching.mevmap ref;
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
type apperror =
  | AE_WrongArgKind of (argkind * argkind)
  | AE_CannotInfer
  | AE_CannotInferMod
  | AE_NotFunctional
  | AE_InvalidArgForm     of invalid_arg_form
  | AE_InvalidArgMod
  | AE_InvalidArgProof    of (form * form)
  | AE_InvalidArgModRestr of EcTyping.restriction_error

and argkind = [`Form | `Mem | `Mod | `PTerm]

and invalid_arg_form =
  | IAF_Mismatch of (ty * ty)
  | IAF_TyError of env * EcTyping.tyerror

type pterror = (LDecl.hyps * EcUnify.unienv * EcMatching.mevmap) * apperror

exception ProofTermError of pterror

(* -------------------------------------------------------------------- *)
let argkind_of_parg arg : argkind option =
  match arg with
  | EA_mod   _ -> Some `Mod
  | EA_mem   _ -> Some `Mem
  | EA_form  _ -> Some `Form
  | EA_proof _ -> Some `PTerm
  | EA_none    -> None

(* -------------------------------------------------------------------- *)
let argkind_of_ptarg arg : argkind =
  match arg with
  | PVAFormula _ -> `Form
  | PVAMemory  _ -> `Mem
  | PVAModule  _ -> `Mod
  | PVASub     _ -> `PTerm

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
    pte_ue = PT.unienv_of_hyps hyps;
    pte_ev = ref EcMatching.MEV.empty; }

(* -------------------------------------------------------------------- *)
let rec get_head_symbol (pt : pt_env) (f : form) =
  match f_node f with
  | Flocal x -> begin
      match MEV.get x `Form !(pt.pte_ev) with
      | Some (`Set (`Form f)) -> get_head_symbol pt f
      | _ -> f
    end
  | _ -> f

(* -------------------------------------------------------------------- *)
let can_concretize (pt : pt_env) =
  EcMatching.can_concretize !(pt.pte_ev) pt.pte_ue

(* -------------------------------------------------------------------- *)
let concretize_env pe =
  CPTEnv (EcMatching.MEV.assubst pe.pte_ue !(pe.pte_ev))

(* -------------------------------------------------------------------- *)
let concretize_e_form (CPTEnv subst) f =
  Fsubst.f_subst subst f

(* -------------------------------------------------------------------- *)
let rec concretize_e_arg ((CPTEnv subst) as cptenv) arg =
  match arg with
  | PAFormula f        -> PAFormula (Fsubst.f_subst subst f)
  | PAMemory  m        -> PAMemory (Mid.find_def m m subst.fs_mem)
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
let tc_pterm_apperror pte ?loc (kind : apperror) =
  let ue = EcUnify.UniEnv.copy pte.pte_ue in
  let pe = !(pte.pte_ev) in
  let hy = pte.pte_hy in
  tc_error_exn ?loc pte.pte_pe (ProofTermError ((hy, ue, pe), kind))

(* -------------------------------------------------------------------- *)
let pt_of_hyp pf hyps x =
  let ptenv = ptenv_of_penv hyps pf in
  let ax    = LDecl.hyp_by_id x hyps in

  { ptev_env = ptenv;
    ptev_pt  = { pt_head = PTLocal x; pt_args = []; };
    ptev_ax  = ax; }

(* -------------------------------------------------------------------- *)
let pt_of_hyp_r ptenv x =
  let ax = LDecl.hyp_by_id x ptenv.pte_hy in

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
let pt_of_global_r ptenv p tys =
  let env = LDecl.toenv ptenv.pte_hy in
  let ax  = EcEnv.Ax.instanciate p tys env in

  { ptev_env = ptenv;
    ptev_pt  = { pt_head = PTGlobal (p, tys); pt_args = []; };
    ptev_ax  = ax; }

(* -------------------------------------------------------------------- *)
let pt_of_handle_r ptenv hd =
  let g = FApi.get_pregoal_by_id hd ptenv.pte_pe in

  { ptev_env = ptenv;
    ptev_pt  = { pt_head = PTHandle hd; pt_args = []; };
    ptev_ax  = g.g_concl; }

(* -------------------------------------------------------------------- *)
let pt_of_uglobal pf hyps p =
  let ptenv   = ptenv_of_penv hyps pf in
  let env     = LDecl.toenv hyps in
  let ax      = oget (EcEnv.Ax.by_path_opt p env) in
  let typ, ax = (ax.EcDecl.ax_tparams, ax.EcDecl.ax_spec) in

  (* FIXME: TC HOOK *)
  let fs  = EcUnify.UniEnv.opentvi ptenv.pte_ue typ None in
  let ax  = Fsubst.subst_tvar fs ax in
  let typ = List.map (fun (a, _) -> EcIdent.Mid.find a fs) typ in

  { ptev_env = ptenv;
    ptev_pt  = { pt_head = PTGlobal (p, typ); pt_args = []; };
    ptev_ax  = ax; }

(* -------------------------------------------------------------------- *)
let get_implicits (hyps : LDecl.hyps) (f : form) : bool list =
  let rec doit acc f =
    match PT.destruct_product hyps f with
    | Some (`Forall (x, GTty _, f)) ->
        doit (`Var x :: acc) f
    | Some (`Forall (_, _, f)) ->
        doit (`Direct false :: acc) f
    | Some (`Imp (_, f)) ->
        doit (`Direct false :: acc) f
    | _ ->
       List.rev_map (function
         | `Var    x -> Mid.mem x f.f_fv
         | `Direct b -> b)
         acc
  in doit [] f

(* -------------------------------------------------------------------- *)
let pattern_form ?name hyps ~ptn subject =
  let dfl () = Printf.sprintf "?%d" (EcUid.unique ()) in

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
    if not mode.fm_conv || not (EcReduction.is_conv pt.pte_hy ptn subject) then
      raise exn

(* -------------------------------------------------------------------- *)
exception FindOccFailure of [`MatchFailure | `IncompleteMatch]

type occmode = {
  k_keyed : bool;
  k_conv  : bool;
}

let rec pf_find_occurence (pt : pt_env) ?occmode ~ptn subject =
  let module E = struct exception MatchFound of form end in

  let occmode = odfl { k_keyed = false; k_conv = true; } occmode in

  let na = List.length (snd (EcFol.destr_app ptn)) in

  let kmatch key tp =
    match key, (fst (destr_app tp)).f_node with
    | `NoKey , _           -> true
    | `Path p, Fop (p', _) -> EcPath.p_equal p p'
    | `Path _, _           -> false
    | `Var  x, Flocal x'   -> id_equal x x'
    | `Var  _, _           -> false
  in

  let keycheck tp key = not occmode.k_keyed || kmatch key tp in

  (* Extract key from pattern *)
  let key =
    match (fst (destr_app ptn)).f_node with
    | Fop (p, _) -> `Path p
    | Flocal x   ->
        if   is_none (EcMatching.MEV.get x `Form !(pt.pte_ev))
        then `Var x
        else `NoKey
    | _ -> `NoKey
  in

  let mode =
    if   key = `NoKey
    then EcMatching.fmrigid
    else EcMatching.fmdelta in

  let mode = { mode with fm_conv = occmode.k_conv } in

  let trymatch mode bds tp =
    if not (keycheck tp key) then `Continue else

    let tp =
      match tp.f_node with
      | Fapp (h, hargs) when List.length hargs > na ->
          let (a1, a2) = List.takedrop na hargs in
            f_app h a1 (toarrow (List.map f_ty a2) tp.f_ty)
      | _ -> tp
    in

    try
      if not (Mid.set_disjoint bds tp.f_fv) then
        `Continue
      else begin
        pf_form_match ~mode pt ~ptn tp;
        raise (E.MatchFound tp)
      end
    with EcMatching.MatchFailure -> `Continue
  in

  let (ue, pe) = (EcUnify.UniEnv.copy pt.pte_ue, !(pt.pte_ev)) in

  try
    ignore (EcMatching.FPosition.select (trymatch mode) subject);
    raise (FindOccFailure `MatchFailure)
  with E.MatchFound subf ->
     if not (can_concretize pt) then begin
       EcUnify.UniEnv.restore ~dst:pt.pte_ue ~src:ue; pt.pte_ev := pe;
       raise (FindOccFailure `IncompleteMatch)
     end;
     subf

(* -------------------------------------------------------------------- *)
let default_modes = [
  { k_keyed =  true; k_conv = false; };
  { k_keyed =  true; k_conv =  true; };
  { k_keyed = false; k_conv =  true; };
]

let pf_find_occurence_lazy (pt : pt_env) ?(modes = default_modes) ~ptn subject =
  let rec doit (modes : occmode list) =
    match modes with
    | [] ->
        assert false
    | [occmode] ->
        (pf_find_occurence pt ~occmode ~ptn subject, occmode)
    | occmode :: modes ->
      try  (pf_find_occurence pt ~occmode ~ptn subject, occmode)
      with FindOccFailure _ -> doit modes in

  doit modes

(* --------------------------------------------------------------------- *)
let pf_find_occurence (pt : pt_env) ?occmode ~ptn subject =
  match occmode with
  | Some occmode -> (pf_find_occurence pt ~occmode ~ptn subject, occmode)
  | None         -> pf_find_occurence_lazy pt ~ptn subject

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
  | ([], x) when LDecl.hyp_exists x hyps && not hastyp ->
      let (x, fp) = LDecl.hyp_by_name x hyps in
        Some (`Local x, ([], fp))

  | _ ->
    match EcEnv.Ax.lookup_opt fp (LDecl.toenv hyps) with
    | Some (p, ({ EcDecl.ax_spec = fp } as ax)) ->
        Some (`Global p, (ax.EcDecl.ax_tparams, fp))
    | _ -> None

(* -------------------------------------------------------------------- *)
(* Try to extract a ffpattern parse-tree from a genpattern parse-tree.
 * This allows to mix proof-terms and formulas/values in tactic
 * arguments. Priority should always been given to ffpattern as it is
 * always possible to force the interpretation of a genpattern as a
 * formula with holes by annotating it with an empty {} occurences
 * selector *)

let ffpattern_of_form hyps fp : ppterm option =
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
          Some ({ fp_mode = `Implicit;
                  fp_head = FPNamed (p, tya);
                  fp_args = List.map ae_of_form args; })
        else
          None

    | _ -> None

let ffpattern_of_genpattern hyps (ge : genpattern) =
  match ge with
  | `ProofTerm pe     -> Some pe
  | `Form (Some _, _) -> None
  | `Form (None, fp)  -> ffpattern_of_form hyps fp
  | `LetIn _          -> None

(* -------------------------------------------------------------------- *)
let process_named_pterm pe (tvi, fp) =
  let env = LDecl.toenv pe.pte_hy in

  let (p, (typ, ax)) =
    match lookup_named_psymbol pe.pte_hy ~hastyp:(tvi <> None) (unloc fp) with
    | Some (p, ax) -> (p, ax)
    | None -> tc_lookup_error pe.pte_pe `Lemma (unloc fp)
  in

  let tvi =
    Exn.recast_pe pe.pte_pe pe.pte_hy
      (fun () -> omap (EcTyping.transtvi env pe.pte_ue) tvi)
  in

  PT.pf_check_tvi pe.pte_pe typ tvi;

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
  let prcut fp =
    match fp with
    | None    -> tc_pterm_apperror pe AE_CannotInfer
    | Some fp -> PT.pf_process_formula pe.pte_pe pe.pte_hy fp
  in process_pterm_cut prcut pe pt

(* ------------------------------------------------------------------ *)
let rec trans_pterm_arg_impl pe f =
  let pt = { pt_head = PTCut f; pt_args = []; } in
  let pt = { ptev_env = pe; ptev_pt = pt; ptev_ax = f; } in
    { ptea_env = pe; ptea_arg = PVASub pt; }

(* ------------------------------------------------------------------ *)
and trans_pterm_arg_value pe ?name { pl_desc = arg; pl_loc = loc; } =
  let dfl () = Printf.sprintf "?%d" (EcUid.unique ()) in
  let name = name |> omap (Printf.sprintf "?%s") in

  match arg with
  | EA_mod _ | EA_mem _ | EA_proof _ ->
      let ak = oget (argkind_of_parg arg) in
      tc_pterm_apperror ~loc pe (AE_WrongArgKind (ak, `Form))

  | EA_none ->
      let aty = EcUnify.UniEnv.fresh pe.pte_ue in
      let x   = EcIdent.create (ofdfl dfl name) in
      pe.pte_ev := EcMatching.MEV.add x `Form !(pe.pte_ev);
      { ptea_env = pe; ptea_arg = PVAFormula (f_local x aty); }

  | EA_form fp ->
      let env = LDecl.toenv pe.pte_hy in
      let ptn = ref Mid.empty in
      let fp  =

      try  EcTyping.trans_pattern env ptn pe.pte_ue fp
      with EcTyping.TyError (loc, env, err) ->
        tc_pterm_apperror ~loc pe (AE_InvalidArgForm (IAF_TyError (env, err)))
      in

      Mid.iter
        (fun x _ -> pe.pte_ev := EcMatching.MEV.add x `Form !(pe.pte_ev))
        !ptn;
      { ptea_env = pe; ptea_arg = PVAFormula fp; }

(* ------------------------------------------------------------------ *)
and trans_pterm_arg_mod pe { pl_desc = arg; pl_loc = loc; } =
  let mp =
    match arg with
    | EA_mod mp ->
       mp

    | EA_none ->
       tc_pterm_apperror ~loc pe AE_CannotInferMod

    | EA_mem _ | EA_proof _ ->
       let ak = oget (argkind_of_parg arg) in
       tc_pterm_apperror ~loc pe (AE_WrongArgKind (ak, `Mod))

    | EA_form fp ->
      match pmsymbol_of_pform fp with
      | None    -> tc_pterm_apperror ~loc pe (AE_WrongArgKind (`Form, `Mod))
      | Some mp -> mk_loc loc mp
  in

  let env  = LDecl.toenv pe.pte_hy in
  let mod_ = (fun () -> EcTyping.trans_msymbol env mp) in
  let mod_ = Exn.recast_pe pe.pte_pe pe.pte_hy mod_ in

    { ptea_env = pe; ptea_arg = PVAModule mod_; }

(* ------------------------------------------------------------------ *)
and trans_pterm_arg_mem pe ?name { pl_desc = arg; pl_loc = loc; } =
  let dfl () = Printf.sprintf "&m%d" (EcUid.unique ()) in

  match arg with
  | EA_form { pl_loc = lc; pl_desc = (PFmem m) } ->
      trans_pterm_arg_mem pe ?name (mk_loc lc (EA_mem m))

  | EA_mod  _ | EA_proof _ | EA_form _ ->
      let ak = oget (argkind_of_parg arg) in
      tc_pterm_apperror ~loc pe (AE_WrongArgKind (ak, `Mem))

  | EA_none ->
      let x = EcIdent.create (ofdfl dfl name) in
      pe.pte_ev := EcMatching.MEV.add x `Mem !(pe.pte_ev);
      { ptea_env = pe; ptea_arg = PVAMemory x; }

  | EA_mem mem ->
      let env = LDecl.toenv pe.pte_hy in
      let mem = (fun () -> EcTyping.transmem env mem) in
      let mem = Exn.recast_pe pe.pte_pe pe.pte_hy mem in
      { ptea_env = pe; ptea_arg = PVAMemory mem; }

(* ------------------------------------------------------------------ *)
and process_pterm_arg
    ?implicits ({ ptev_env = pe } as pt) ({ pl_loc = loc; } as arg)
=
  match PT.destruct_product pe.pte_hy (get_head_symbol pe pt.ptev_ax) with
  | None -> tc_pterm_apperror ~loc pe AE_NotFunctional

  | Some (`Imp (f, _)) -> begin
      match unloc arg with
      | EA_none -> trans_pterm_arg_impl pe f

      | EA_form fp -> begin
          match ffpattern_of_form pe.pte_hy fp with
          | None ->
              tc_pterm_apperror ~loc pe (AE_WrongArgKind (`Form, `PTerm))

          | Some fp ->
              { ptea_env = pe;
                ptea_arg = PVASub (process_full_pterm ?implicits pe fp); }
      end

      | EA_proof fp ->
          { ptea_env = pe;
            ptea_arg = PVASub (process_full_pterm ?implicits pe fp); }

      | EA_mem _ | EA_mod _ ->
          let ak = oget (argkind_of_parg (unloc arg)) in
          tc_pterm_apperror ~loc pe (AE_WrongArgKind (ak, `PTerm))
  end

  | Some (`Forall (x, xty, _)) -> begin
      match xty with
      | GTty    _ -> trans_pterm_arg_value pe ~name:(EcIdent.name x) arg
      | GTmodty _ -> trans_pterm_arg_mod pe arg
      | GTmem   _ -> trans_pterm_arg_mem pe arg
  end

(* -------------------------------------------------------------------- *)
and hole_for_impl  pe f = trans_pterm_arg_impl  pe f
and hole_for_mem   pe   = trans_pterm_arg_mem   pe (L.mk_loc L._dummy EA_none)
and hole_for_mod   pe   = trans_pterm_arg_mod   pe (L.mk_loc L._dummy EA_none)
and hole_for_value pe   = trans_pterm_arg_value pe (L.mk_loc L._dummy EA_none)

(* -------------------------------------------------------------------- *)
and dfl_arg_for_impl  pe f arg = ofdfl (fun () -> (hole_for_impl  pe f).ptea_arg) arg
and dfl_arg_for_mem   pe   arg = ofdfl (fun () -> (hole_for_mem   pe  ).ptea_arg) arg
and dfl_arg_for_mod   pe   arg = ofdfl (fun () -> (hole_for_mod   pe  ).ptea_arg) arg
and dfl_arg_for_value pe   arg = ofdfl (fun () -> (hole_for_value pe  ).ptea_arg) arg

(* -------------------------------------------------------------------- *)
and check_pterm_oarg ?loc pe (x, xty) f arg =
  let env = LDecl.toenv (pe.pte_hy) in

  match xty with
  | GTty xty -> begin
      match dfl_arg_for_value pe arg with
      | PVAFormula arg -> begin
        try
          pf_unify pe xty arg.f_ty;
          (Fsubst.f_subst_local x arg f, PAFormula arg)
        with EcUnify.UnificationFailure _ ->
          tc_pterm_apperror ?loc pe
            (AE_InvalidArgForm (IAF_Mismatch (arg.f_ty, xty)))
      end
      | arg ->
         let ak = argkind_of_ptarg arg in
         tc_pterm_apperror ?loc pe (AE_WrongArgKind (ak, `Form))
  end

  | GTmem _ -> begin
      match dfl_arg_for_mem pe arg with
      | PVAMemory arg -> (Fsubst.f_subst_mem x arg f, PAMemory arg)
      | arg ->
         let ak = argkind_of_ptarg arg in
         tc_pterm_apperror ?loc pe (AE_WrongArgKind (ak, `Mem))
  end

  | GTmodty (emt, restr) -> begin
      match dfl_arg_for_mod pe arg with
      | PVAModule (mp, mt) -> begin
        try
          EcTyping.check_modtype_with_restrictions env mp mt emt restr;
          EcPV.check_module_in env mp emt;
          (Fsubst.f_subst_mod x mp f, PAModule (mp, mt))
        with
        | EcTyping.TymodCnvFailure _ ->
            tc_pterm_apperror ?loc pe AE_InvalidArgMod
        | EcTyping.RestrictionError (_, e) ->
            tc_pterm_apperror ?loc pe (AE_InvalidArgModRestr e)
      end
      | arg ->
         let ak = argkind_of_ptarg arg in
         tc_pterm_apperror ?loc pe (AE_WrongArgKind (ak, `Mod))
  end

(* -------------------------------------------------------------------- *)
and check_pterm_arg ?loc pe (x, xty) f arg =
  check_pterm_oarg ?loc pe (x, xty) f (Some arg)

(* -------------------------------------------------------------------- *)
and apply_pterm_to_oarg ?loc ({ ptev_env = pe; ptev_pt = rawpt; } as pt) oarg =
  assert (odfl true (oarg |> omap (fun arg -> pe == arg.ptea_env)));

  let oarg = oarg |> omap (fun arg -> arg.ptea_arg) in


  match PT.destruct_product pe.pte_hy (get_head_symbol pe pt.ptev_ax) with
  | None   -> tc_pterm_apperror ?loc pe AE_NotFunctional
  | Some t ->
      let (newax, newarg) =
        match t with
        | `Imp (f1, f2) -> begin
            match dfl_arg_for_impl pe f1 oarg with
            | PVASub arg -> begin
              try
                pf_form_match ~mode:EcMatching.fmdelta pe ~ptn:f1 arg.ptev_ax;
                (f2, PASub (Some arg.ptev_pt))
              with EcMatching.MatchFailure ->
                tc_pterm_apperror ?loc pe (AE_InvalidArgProof (arg.ptev_ax, f1))
            end
            | arg ->
               let ak = argkind_of_ptarg arg in
               tc_pterm_apperror ?loc pe (AE_WrongArgKind (ak, `Form))
        end

        | `Forall (x, xty, f) ->
             check_pterm_oarg ?loc pe (x, xty) f oarg
      in

      let rawargs = rawpt.pt_args @ [newarg] in
      { pt with ptev_ax = newax; ptev_pt = { rawpt with pt_args = rawargs } }

(* -------------------------------------------------------------------- *)
and apply_pterm_to_arg ?loc pt arg =
  apply_pterm_to_oarg ?loc pt (Some arg)

(* -------------------------------------------------------------------- *)
and apply_pterm_to_arg_r ?loc pt arg =
  let arg = { ptea_arg = arg; ptea_env = pt.ptev_env; } in
  apply_pterm_to_arg ?loc pt arg

(* -------------------------------------------------------------------- *)
and apply_pterm_to_hole ?loc pt =
  apply_pterm_to_oarg ?loc pt None

(* -------------------------------------------------------------------- *)
and apply_pterm_to_holes ?loc n pt =
  EcUtils.iterop (apply_pterm_to_hole ?loc) n pt

(* -------------------------------------------------------------------- *)
and process_implicits ip ({ ptev_pt = pt; ptev_env = env; } as pe) =
  match ip with
  | [] -> ([], pe)
  | b :: ip ->
      if not b then ((b :: ip), pe) else
        match PT.destruct_product ~reduce:false env.pte_hy pe.ptev_ax with
        | Some (`Forall (x, xty, f)) ->
            let (newax, newarg) = check_pterm_oarg env (x, xty) f None in
            let pt = { pt with pt_args = pt.pt_args @ [newarg] } in
            let pe = { pe with ptev_ax = newax; ptev_pt = pt } in
            process_implicits ip pe
        | _ -> ((b :: ip), pe)

(* -------------------------------------------------------------------- *)
and process_pterm_arg_app ?implicits ?(ip = []) pt ({ pl_loc = loc } as arg) =
  let ip, pt = process_implicits ip pt in
  let ip = odfl [] (List.otail ip) in
  (apply_pterm_to_arg ~loc pt (process_pterm_arg ?implicits pt arg), ip)

(* -------------------------------------------------------------------- *)
and process_pterm_args_app ?implicits ?(ip = []) pt args =
  List.fold_left
    (fun (pt, ip) arg ->
       process_pterm_arg_app ?implicits ~ip pt arg)
    (pt, ip) args

(* -------------------------------------------------------------------- *)
and process_full_pterm ?(implicits = false) pe pf =
  let pt = process_pterm pe pf.fp_head in
  if List.is_empty pf.fp_args then pt else
    let ip =
      match implicits && pf.fp_mode = `Implicit with
      | true  -> get_implicits pt.ptev_env.pte_hy pt.ptev_ax
      | false -> []
    in fst (process_pterm_args_app ~implicits ~ip pt pf.fp_args)

(* -------------------------------------------------------------------- *)
let process_full_pterm_cut ~prcut pe pf =
  let pt = process_pterm_cut ~prcut pe pf.fp_head in
  fst (process_pterm_args_app pt pf.fp_args)

(* -------------------------------------------------------------------- *)
let process_full_closed_pterm_cut ~prcut pe pf =
  let pt = process_pterm_cut ~prcut pe pf.fp_head in
  let pt = fst (process_pterm_args_app pt pf.fp_args) in
    (* FIXME: use core exception? *)
    if not (can_concretize pe) then
      tc_error pe.pte_pe "cannot infer all placeholders";
    concretize pt

(* -------------------------------------------------------------------- *)
let process_full_closed_pterm pe pf =
  let pt = process_pterm pe pf.fp_head in
  let pt = fst (process_pterm_args_app pt pf.fp_args) in
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
let tc1_process_full_pterm_cut ~prcut (tc : tcenv1) (ff : 'a gppterm) =
  let pe   = FApi.tc1_penv tc in
  let hyps = FApi.tc1_hyps tc in
  process_full_pterm_cut ~prcut (ptenv_of_penv hyps pe) ff

(* -------------------------------------------------------------------- *)
let tc1_process_full_pterm ?implicits (tc : tcenv1) (ff : ppterm) =
  let pe   = FApi.tc1_penv tc in
  let hyps = FApi.tc1_hyps tc in
  process_full_pterm ?implicits (ptenv_of_penv hyps pe) ff

(* -------------------------------------------------------------------- *)
let tc1_process_full_closed_pterm_cut ~prcut (tc : tcenv1) (ff : 'a gppterm) =
  let pe   = FApi.tc1_penv tc in
  let hyps = FApi.tc1_hyps tc in
  process_full_closed_pterm_cut ~prcut (ptenv_of_penv hyps pe) ff

(* -------------------------------------------------------------------- *)
let tc1_process_full_closed_pterm (tc : tcenv1) (ff : ppterm) =
  let pe   = FApi.tc1_penv tc in
  let hyps = FApi.tc1_hyps tc in
  process_full_closed_pterm (ptenv_of_penv hyps pe) ff

(* -------------------------------------------------------------------- *)
type prept = [
  | `Hy   of EcIdent.t
  | `G    of EcPath.path * ty list
  | `UG   of EcPath.path
  | `HD   of handle
  | `App  of prept * prept_arg list
]

and prept_arg =  [
  | `F   of form
  | `Mem of EcMemory.memory
  | `Mod of (EcPath.mpath * EcModules.module_sig)
  | `Sub of prept
  | `H_
]

(* -------------------------------------------------------------------- *)
let pt_of_prept tc (pt : prept) =
  let ptenv = ptenv_of_penv (FApi.tc1_hyps tc) !!tc in

  let rec build_pt = function
    | `Hy  id         -> pt_of_hyp_r ptenv id
    | `G   (p, tys)   -> pt_of_global_r ptenv p tys
    | `UG  p          -> pt_of_global_r ptenv p []
    | `HD  hd         -> pt_of_handle_r ptenv hd
    | `App (pt, args) -> List.fold_left app_pt_ev (build_pt pt) args

  and app_pt_ev pt_ev = function
    | `F f    -> apply_pterm_to_arg_r pt_ev (PVAFormula f)
    | `Mem m  -> apply_pterm_to_arg_r pt_ev (PVAMemory m)
    | `Mod m  -> apply_pterm_to_arg_r pt_ev (PVAModule m)
    | `Sub pt -> apply_pterm_to_arg_r pt_ev (PVASub (build_pt pt))
    | `H_     -> apply_pterm_to_hole pt_ev

  in build_pt pt

(* -------------------------------------------------------------------- *)
module Prept = struct
  let (@) f args = `App (f, args)

  let hyp   h     = `Hy h
  let glob  g tys = `G (g, tys)
  let uglob g     = `UG g
  let hdl   h     = `HD h

  let aform f   = `F f
  let amem m    = `Mem m
  let amod mp s = `Mod(mp,s)
  let asub pt   = `Sub pt
  let h_        = `H_
  let ahyp h    = asub (hyp h)
  let ahdl h    = asub (hdl h)
end
