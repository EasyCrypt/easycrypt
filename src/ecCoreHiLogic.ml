(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcSymbols
open EcPath
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcBaseLogic
open EcLogic
open EcMetaProg

module TT = EcTyping

module Sid = EcIdent.Sid
module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
let unienv_of_hyps hyps =
  EcUnify.UniEnv.create (Some (LDecl.tohyps hyps).h_tvar)

(* -------------------------------------------------------------------- *)
let process_tyargs hyps tvi =
  let ue = unienv_of_hyps hyps in
    omap (TT.transtvi (LDecl.toenv hyps) ue) tvi

(* -------------------------------------------------------------------- *)
let process_form_opt hyps pf oty =
  let ue  = unienv_of_hyps hyps in
  let ff  = TT.trans_form_opt (LDecl.toenv hyps) ue pf oty in
    EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) ff

(* -------------------------------------------------------------------- *)
let process_form hyps pf ty =
  process_form_opt hyps pf (Some ty)

(* -------------------------------------------------------------------- *)
let process_formula hyps pf =
  process_form hyps pf tbool

(* -------------------------------------------------------------------- *)
let process_exp hyps e oty =
  let env = LDecl.toenv hyps in
  let ue  = EcUnify.UniEnv.create (Some (LDecl.tohyps hyps).h_tvar) in
  let e   =  TT.transexpcast_opt env ue oty e in
  EcTypes.e_uni (EcUnify.UniEnv.close ue) e

(* -------------------------------------------------------------------- *)
type pterm_parg =
  [ `FormOrMod of form option * (mpath * module_sig) option
  | `Memory    of EcIdent.t ]

type 'a pterm_arg =
  [ `KnownMem   of EcIdent.t * EcIdent.t
  | `KnownMod   of EcIdent.t * (mpath * module_sig)
  | `KnownVar   of EcIdent.t * form
  | `SideCond   of EcFol.form
  | `UnknownVar of EcIdent.t * 'a ]

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

(* -------------------------------------------------------------------- *)
let trans_pterm_argument hyps ue arg =
  let env = LDecl.toenv hyps in

  match unloc arg with
  | EA_form fp -> begin
      let ff =
        try  `Form (TT.trans_form_opt env ue fp None)
        with TT.TyError _ as e -> `Error e
      in

      let mm =
        match pmsymbol_of_pform fp with
        | None    -> `Error None
        | Some mp ->
            try
              let (mp, mt) = TT.trans_msymbol env (mk_loc arg.pl_loc mp) in
                `Mod (mp, mt)
            with TT.TyError _ as e -> `Error (Some e)
      in

      match ff, mm with
      | `Error e, `Error _ -> raise e
      | `Form  f, `Mod   m -> Some (`FormOrMod (Some f, Some m))
      | `Form  f, `Error _ -> Some (`FormOrMod (Some f, None  ))
      | `Error _, `Mod   m -> Some (`FormOrMod (None  , Some m))
  end
      
  | EA_mem mem ->
      let mem = TT.transmem env mem in
        Some (`Memory mem)

  | EA_none ->
      None

  | EA_mod mp ->
    let m = TT.trans_msymbol env mp in
    Some (`FormOrMod (None, Some m))

(* -------------------------------------------------------------------- *)
let process_named_pterm _loc hyps (fp, tvi) =
  let env = LDecl.toenv hyps in

  let (p, typ, ax) =
    match unloc fp with
    | ([], x) when LDecl.has_hyp x hyps ->
        let (x, fp) = LDecl.lookup_hyp x hyps in
          (`Local x, [], fp)

    | _ -> begin
      match EcEnv.Ax.lookup_opt (unloc fp) env with
      | Some (p, ({ EcDecl.ax_spec = Some fp } as ax)) ->
          (`Global p, ax.EcDecl.ax_tparams, fp)

      | _ -> tacuerror "cannot find lemma %s" (string_of_qsymbol (unloc fp))
    end
  in

  let ue  = unienv_of_hyps hyps in
  let tvi = omap (TT.transtvi env ue) tvi in

  begin
    match tvi with
    | None -> ()

    | Some (EcUnify.UniEnv.TVIunamed tyargs) ->
        if List.length tyargs <> List.length typ then
          tacuerror
            "wrong number of type parameters (%d, expecting %d)"
            (List.length tyargs) (List.length typ)

    | Some (EcUnify.UniEnv.TVInamed tyargs) ->
        let typnames = List.map EcIdent.name typ in

        List.iter
          (fun (x, _) ->
             if not (List.mem x typnames) then
               tacuerror "unknown type variable: %s" x)
          tyargs
  end;

  let fs  = EcUnify.UniEnv.freshen_ue ue typ tvi in
  let ax  = Fsubst.subst_tvar fs ax in
  let typ = List.map (fun a -> EcIdent.Mid.find a fs) typ in

    (p, typ, ue, ax)

(* -------------------------------------------------------------------- *)
let process_pterm loc prcut hyps pe =
  match pe.fp_kind with
  | FPNamed (fp, tyargs) ->
      process_named_pterm loc hyps (fp, tyargs)

  | FPCut fp ->
      let fp = prcut fp in
      let ue = unienv_of_hyps hyps in
        (`Cut fp, [], ue, fp)

(* -------------------------------------------------------------------- *)
let check_pterm_arg_for_ty hyps ty arg =
  let ue  = unienv_of_hyps hyps in
  let env = LDecl.toenv hyps in

  let error () = 
    tacuerror ~loc:arg.pl_loc "invalid argument type"
  in

  match arg.pl_desc, ty with
  | EA_form pf, Some (GTty ty) ->
      let ff = TT.trans_form env ue pf ty in
        AAform (EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) ff)

  | EA_mem mem, Some (GTmem _) ->
      AAmem (TT.transmem env mem)

  | EA_none, None ->
      AAnode

  | EA_form fp, Some (GTmodty _) -> begin
    match pmsymbol_of_pform fp with
    | None    -> error ()
    | Some mp ->
        let (mp, mt) = TT.trans_msymbol env (mk_loc arg.pl_loc mp) in
          AAmp (mp, mt)
  end

  | _, _ -> error ()

(* -------------------------------------------------------------------- *)
let check_pterm_argument hyps ue f arg =
  let env = LDecl.toenv hyps in

  let invalid_arg () = tacuerror "wrongly applied lemma" in

  match arg, destruct_product hyps f with
  | None, Some (`Imp (f1, f2)) ->
      (f2, `SideCond f1)

  | None, Some (`Forall (x, gty, f)) -> begin
      match gty with
      | GTmodty _  -> tacuerror "cannot infer module"
      | GTmem   _  -> tacuerror "cannot infer memory"
      | GTty    ty -> (f, `UnknownVar (x, ty))
  end

  | Some (`FormOrMod (Some tp, _)),
    Some (`Forall (x, GTty ty, f)) -> begin
      try
        EcUnify.unify env ue tp.f_ty ty;
        (Fsubst.f_subst_local x tp f, `KnownVar (x, tp))
      with EcUnify.UnificationFailure _ ->
        invalid_arg ()
  end

  | Some (`Memory m),
    Some (`Forall (x, GTmem _, f)) ->
      (Fsubst.f_subst_mem x m f, `KnownMem (x, m))

  | Some (`FormOrMod (_, Some (mp, mt))),
    Some (`Forall (x, GTmodty (emt, restr), f)) ->
      check_modtype_restr env mp mt emt restr;
      (Fsubst.f_subst_mod x mp f, `KnownMod (x, (mp, mt)))

  | _, _ -> invalid_arg ()

(* -------------------------------------------------------------------- *)
let check_pterm_arguments hyps ue ax args =
  let (ax, ids) = List.map_fold (check_pterm_argument hyps ue) ax args in
    (ax, List.rev ids)

(* -------------------------------------------------------------------- *)
let can_concretize_pterm_arguments (tue, ev) ids =
  let is_known_id = function
    | `UnknownVar (x, _) -> begin
      match EV.get x ev with Some (`Set _) -> true | _ -> false
    end
    | _ -> true
  in
     EcUnify.UniEnv.closed tue && List.for_all is_known_id ids

(* -------------------------------------------------------------------- *)
let evmap_of_pterm_arguments ids =
  let forid id ev =
    match id with
    | `UnknownVar (x, _) -> EV.add x ev
    | _ -> ev
  in
    List.fold_right forid ids EV.empty

(* -------------------------------------------------------------------- *)
let concretize_pterm_arguments (tue, ev) ids =
  let do1 = function
    | `KnownMod   (_, (mp, mt)) -> EcLogic.AAmp   (mp, mt)
    | `KnownMem   (_, mem)      -> EcLogic.AAmem  mem
    | `KnownVar   (_, tp)       -> EcLogic.AAform (Fsubst.uni tue tp)
    | `SideCond   _             -> EcLogic.AAnode
    | `UnknownVar (x, _)        -> EcLogic.AAform (Fsubst.uni tue (EV.doget x ev))
  in
    List.rev (List.map do1 ids)

(* -------------------------------------------------------------------- *)
let concretize_form (tue, ev) f =
  let s = Fsubst.f_subst_init false Mid.empty { ty_subst_id with ts_u = tue } Mp.empty in
  let s = EV.fold (fun x f s -> Fsubst.f_bind_local s x f) ev s in
    Fsubst.f_subst s f

(* -------------------------------------------------------------------- *)
let concretize_pterm (tue, ev) ids fp =
  let subst =
    List.fold_left
      (fun subst id ->
        match id with
        | `KnownMod (x, (mp, _)) -> Fsubst.f_bind_mod   subst x mp
        | `KnownMem (x, mem)     -> Fsubst.f_bind_mem   subst x mem
        | `KnownVar (x, tp)      -> Fsubst.f_bind_local subst x (Fsubst.uni tue tp)
        | `UnknownVar (x, _)     -> Fsubst.f_bind_local subst x (Fsubst.uni tue (EV.doget x ev))
        | `SideCond _            -> subst)
      Fsubst.f_subst_id ids
  in
    Fsubst.f_subst subst (Fsubst.uni tue fp)

(* -------------------------------------------------------------------- *)
let process_mkn_apply prcut pe ((juc, _) as g) = 
  let hyps = get_hyps g in

  let (p, typs, ue, ax) = process_pterm _dummy prcut hyps pe in
  let args = List.map (trans_pterm_argument hyps ue) pe.fp_args in
  let (_ax, ids) = check_pterm_arguments hyps ue ax args in

  let (tue, ev) =
    if not (can_concretize_pterm_arguments (ue, EV.empty) ids) then
      tacuerror "cannot find instance";
    (EcUnify.UniEnv.close ue, EV.empty)
  in

  let args = concretize_pterm_arguments (tue, ev) ids in
  let typs = List.map (Tuni.subst tue) typs in

  let ((juc, fn), fgs) =
    match p with
    | `Local  x -> (mkn_hyp  juc hyps x, [])
    | `Global x -> (mkn_glob juc hyps x typs, [])
    | `Cut    x -> let (juc, fn) = new_goal juc (hyps, x) in ((juc, fn), [fn])
  in

  let (juc, an), ags = mkn_apply (fun _ _ a -> a) (juc, fn) args in

    ((juc, an), fgs @ ags)
