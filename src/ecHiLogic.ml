(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcLocation
open EcSymbols
open EcParsetree
open EcTypes
open EcModules
open EcFol

open EcMetaProg
open EcBaseLogic
open EcEnv
open EcLogic
open EcPhl

module Sp = EcPath.Sp

module TT = EcTyping
module UE = EcUnify.UniEnv

(* -------------------------------------------------------------------- *)
type hitenv = {
  hte_provers : EcParsetree.pprover_infos -> EcProvers.prover_infos;
  hte_smtmode : [`Admit | `Strict | `Standard];
}

(* -------------------------------------------------------------------- *)
type tac_error =
  | UnknownHypSymbol of symbol
  | UnknownAxiom     of qsymbol
  | UnknownOperator  of qsymbol
  | BadTyinstance
  | NothingToIntro
  | FormulaExpected
  | MemoryExpected
  | UnderscoreExpected
  | ModuleExpected
  | ElimDoNotWhatToDo
  | NoCurrentGoal

exception TacError of tac_error

let pp_tac_error fmt =
  function
    | UnknownHypSymbol s ->
      Format.fprintf fmt "Unknown hypothesis or logical variable %s" s
    | UnknownAxiom qs ->
      Format.fprintf fmt "Unknown axioms or hypothesis : %a"
        pp_qsymbol qs
    | UnknownOperator qs ->
      Format.fprintf fmt "Unknown operator or logical variable %a"
        pp_qsymbol qs
    | BadTyinstance ->
      Format.fprintf fmt "Invalid type instance"
    | NothingToIntro ->
      Format.fprintf fmt "Nothing to introduce"
    | FormulaExpected ->
      Format.fprintf fmt "formula expected"
    | MemoryExpected ->
      Format.fprintf fmt "Memory expected"
    | UnderscoreExpected ->
      Format.fprintf fmt "_ expected"
    | ModuleExpected ->
      Format.fprintf fmt "module expected"
    | ElimDoNotWhatToDo ->
      Format.fprintf fmt "Elim : do not known what to do"
    | NoCurrentGoal ->
      Format.fprintf fmt "No current goal"

let _ = EcPException.register (fun fmt exn ->
  match exn with
  | TacError e -> pp_tac_error fmt e
  | _ -> raise exn)

let error loc e = EcLocation.locate_error loc (TacError e)

(* -------------------------------------------------------------------- *)
let process_trivial ((juc, n) as g) =
  let t =
    t_seq
      (t_progress (t_id None))
      (t_try t_assumption)
  in
    match t (juc, n) with
    | (juc, []) -> (juc, [])
    | (_  , _ ) -> t_id None g

(* -------------------------------------------------------------------- *)
let process_congr g =
  let (hyps, concl) = get_goal g in

  if not (EcFol.is_eq concl) then
    tacuerror "congr: goal must be an equality";

  let (f1, f2) = EcFol.destr_eq concl in

  match f1.f_node, f2.f_node with
  | Fapp (o1, a1), Fapp (o2, a2)
      when    EcReduction.is_alpha_eq hyps o1 o2
           && List.length a1 = List.length a2 ->
    t_congr o1 ((List.combine a1 a2), f1.f_ty) g

  | _, _ when EcReduction.is_alpha_eq hyps f1 f2 ->
    t_congr f1 ([], f1.f_ty) g

  | _, _ -> tacuerror "congr: no congruence"

(* -------------------------------------------------------------------- *)
let process_tyargs hyps tvi =
  let ue = EcUnify.UniEnv.create (Some (LDecl.tohyps hyps).h_tvar) in
    omap tvi (TT.transtvi (LDecl.toenv hyps) ue)

(* -------------------------------------------------------------------- *)
let process_instanciate hyps ({pl_desc = pq; pl_loc = loc} ,tvi) =
  let env = LDecl.toenv hyps in
  let (p, ax) =
    try EcEnv.Ax.lookup pq env
    with _ -> error loc (UnknownAxiom pq) in
  let args = process_tyargs hyps tvi in
  let args =
    match ax.EcDecl.ax_tparams, args with
    | [], None -> []
    | [], Some _ -> error loc BadTyinstance
    | ltv, Some (UE.TVIunamed l) ->
        if not (List.length ltv = List.length l) then error loc BadTyinstance;
        l
    | ltv, Some (UE.TVInamed l) ->
        let get id =
          try List.assoc (EcIdent.name id) l
          with _ -> error loc BadTyinstance in
        List.map get ltv
    | _, None -> error loc BadTyinstance in
  p,args

(* -------------------------------------------------------------------- *)
let process_global loc tvi g =
  let hyps = get_hyps g in
  let p, tyargs = process_instanciate hyps tvi in
  set_loc loc t_glob p tyargs g

(* -------------------------------------------------------------------- *)
let process_assumption loc (pq, tvi) g =
  let hyps,concl = get_goal g in
  match pq with
  | None ->
      if (tvi <> None) then error loc BadTyinstance;
      let h  =
        try  find_in_hyps concl hyps
        with Not_found -> tacuerror "no assumptions"
      in
      t_hyp h g
  | Some pq ->
      match unloc pq with
      | ([],ps) when LDecl.has_hyp ps hyps ->
          if (tvi <> None) then error pq.pl_loc BadTyinstance;
          set_loc loc (t_hyp (fst (LDecl.lookup_hyp ps hyps))) g
      | _ -> process_global loc (pq,tvi) g

(* -------------------------------------------------------------------- *)
let process_intros pis (juc, n) =
  let mk_id s = lmap (fun s -> EcIdent.create (odfl "_" s)) s in

  let elim_top g =
    let h       = EcIdent.create "_" in
    let (g, an) = EcLogic.t_intros_1 [h] g in
    let (g, n)  = mkn_hyp g (get_hyps (g, an)) h in
    let f       = snd (get_node (g, n)) in
      t_on_goals
        (t_clear (EcIdent.Sid.of_list [h]))
        (t_on_first (t_use n []) (t_elim f (g, an)))
  in

  let rec collect acc core pis =
    match pis, core with
    | [], [] -> acc
    | [], _  -> `Core (List.rev core) :: acc

    | IPCore x :: pis, _  -> collect acc (x :: core) pis
    | IPDone   :: pis, [] -> collect (`Done :: acc) [] pis
    | IPDone   :: pis, _  ->
        let acc = `Core (List.rev core) :: acc in
        let acc = `Done :: acc in
          collect acc [] pis

    | IPCase x :: pis, core  -> begin
        let x   = List.map (collect [] []) x in
          match core with
          | [] -> collect (`Case x :: acc) [] pis
          | _  -> collect (`Case x :: `Core (List.rev core) :: acc) [] pis
    end
  in

  let rec dointro pis (gs : goals) =
    List.fold_left
      (fun gs ip ->
        match ip with
        | `Core ids -> t_on_goals (t_intros (List.map mk_id ids)) gs
        | `Done     -> t_on_goals process_trivial gs
        | `Case pis ->
            let t gs = t_subgoal (List.map dointro1 pis) (elim_top gs) in
              t_on_goals t gs)
      gs pis

  and dointro1 pis (juc, n) = dointro pis (juc, [n]) in

    dointro1 (List.rev (collect [] [] pis)) (juc, n)

(* -------------------------------------------------------------------- *)
let process_elim_arg hyps oty a =
  let ue  = EcUnify.UniEnv.create (Some (LDecl.tohyps hyps).h_tvar) in
  let env = LDecl.toenv hyps in
  match a.pl_desc, oty with
  | EA_form pf, Some (GTty ty) ->
    let ff = TT.transform env ue pf ty in
    AAform (EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) ff)
  | _, Some (GTty _) ->
    error a.pl_loc FormulaExpected
  | EA_mem mem, Some (GTmem _) ->
    AAmem (TT.transmem env mem)
  | _, Some (GTmem _)->
    error a.pl_loc MemoryExpected
  | EA_none, None ->
    AAnode
  | EA_mp mp , Some (GTmodty _) ->
    let (mp, mt) = TT.trans_msymbol env (mk_loc a.pl_loc mp) in
      AAmp (mp, mt)
  | _, Some (GTmodty _) ->
    error a.pl_loc ModuleExpected
  | _, None ->
    error a.pl_loc UnderscoreExpected

(* -------------------------------------------------------------------- *)
let process_form_opt hyps pf oty =
  let ue  = EcUnify.UniEnv.create (Some (LDecl.tohyps hyps).h_tvar) in
  let ff  = TT.transform_opt (LDecl.toenv hyps) ue pf oty in
  EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) ff

(* -------------------------------------------------------------------- *)
let process_form hyps pf ty =
  process_form_opt hyps pf (Some ty)

(* -------------------------------------------------------------------- *)
let process_formula g pf =
  process_form (get_hyps g) pf tbool

(* -------------------------------------------------------------------- *)
let process_mkn_apply process_cut pe (juc, _ as g) = 
  let hyps = get_hyps g in
  let args = pe.fp_args in
  let (juc,fn), fgs =
    match pe.fp_kind with
    | FPNamed (pq,tvi) ->
      begin match unloc pq with
      | ([],ps) when LDecl.has_hyp ps hyps ->
        (* FIXME warning if tvi is not None *)
        let id,_ = LDecl.lookup_hyp ps hyps in
        mkn_hyp juc hyps id, []
      | _ ->
        let p,tys = process_instanciate hyps (pq,tvi) in
        mkn_glob juc hyps p tys, []
      end
    | FPCut pf ->
      let f = process_cut g pf in
      let juc, fn = new_goal juc (hyps, f) in
      (juc,fn), [fn]
  in
  let (juc,an), ags = mkn_apply process_elim_arg (juc,fn) args in
  (juc,an), fgs@ags

(* -------------------------------------------------------------------- *)
let process_smt hitenv pi g =
  let pi = hitenv.hte_provers pi in

  match hitenv.hte_smtmode with
  | `Admit    -> t_admit g
  | `Standard -> t_seq (t_simplify_nodelta) (t_smt false pi) g
  | `Strict   -> t_seq (t_simplify_nodelta) (t_smt true  pi) g

(* -------------------------------------------------------------------- *)
let process_cut name phi g =
  let phi = process_formula g phi in
  t_on_last
    (process_intros [IPCore (lmap (fun x -> Some x) name)])
    (t_cut phi g)

(* -------------------------------------------------------------------- *)
let process_generalize l =
  let pr1 pf g =
    let hyps = get_hyps g in
    match pf.pl_desc with
    | PFident({pl_desc = ([],s)},None) when LDecl.has_symbol s hyps ->
      let id = fst (LDecl.lookup s hyps) in
      t_generalize_hyp id g
    | _ ->
      let f = process_form_opt hyps pf None in
      t_generalize_form None f g in
  t_lseq (List.rev_map pr1 l)

(* -------------------------------------------------------------------- *)
let process_clear l g =
  let hyps = get_hyps g in
  let toid ps =
    let s = ps.pl_desc in
    if LDecl.has_symbol s hyps then (fst (LDecl.lookup s hyps))
    else error ps.pl_loc (UnknownHypSymbol s) in
  let ids = EcIdent.Sid.of_list (List.map toid l) in
  t_clear ids g

(* -------------------------------------------------------------------- *)
let process_exists fs g =
  gen_t_exists process_elim_arg fs g

(* -------------------------------------------------------------------- *)
let process_change pf g =
  let f = process_formula g pf in
  set_loc pf.pl_loc (t_change f) g

(* -------------------------------------------------------------------- *)
let process_simplify ri g =
  let env,hyps,_ = get_goal_e g in
  let delta_p, delta_h =
    match ri.pdelta with
    | None -> None, None
    | Some l ->
      let sop = ref Sp.empty and sid = ref EcIdent.Sid.empty in
      let do1 ps =
        match ps.pl_desc with
        | ([],s) when LDecl.has_symbol s hyps ->
          let id = fst (LDecl.lookup s hyps) in
          sid := EcIdent.Sid.add id !sid;
        | qs ->
          let p =
            try EcEnv.Op.lookup_path qs env
            with _ -> error ps.pl_loc (UnknownOperator qs) in
          sop := Sp.add p !sop in
      List.iter do1 l;
      Some !sop, Some !sid in
  let ri = {
    EcReduction.beta    = ri.pbeta;
    EcReduction.delta_p = delta_p;
    EcReduction.delta_h = delta_h;
    EcReduction.zeta    = ri.pzeta;
    EcReduction.iota    = ri.piota;
    EcReduction.logic   = ri.plogic; 
    EcReduction.modpath = ri.pmodpath;
  } in
  t_simplify ri g

(* -------------------------------------------------------------------- *)
let process_elimT loc (pf,qs) g =
  let env,hyps,_ = get_goal_e g in
  let p = set_loc qs.pl_loc (EcEnv.Ax.lookup_path qs.pl_desc) env in
  let f = process_form_opt hyps pf None in
  t_seq (set_loc loc (t_elimT f p))
    (t_simplify EcReduction.beta_red) g

(* -------------------------------------------------------------------- *)
let process_subst loc ri g =
  if ri = [] then t_subst_all g
  else
    let hyps = get_hyps g in
    let totac ps =
      let f = process_form_opt hyps ps None in
      try t_subst1 (Some f) 
      with _ -> assert false (* FIXME error message *) in
    let tacs = List.map totac ri in
    set_loc loc (t_lseq tacs) g

(* -------------------------------------------------------------------- *)
let process_field (p,t,i,m,z,o,e) g =
  let (hyps,concl) = get_goal g in
    (match concl.f_node with
      | Fapp(eq',[arg1;arg2]) ->
        let ty = f_ty arg1 in
        let eq = process_form hyps e (tfun ty (tfun ty tbool)) in
        if (f_equal eq eq' ) then
          let p' = process_form hyps p (tfun ty (tfun ty ty)) in 
          let t' = process_form hyps t (tfun ty (tfun ty ty)) in 
          let i' = process_form hyps i (tfun ty ty) in 
          let m' = process_form hyps m (tfun ty ty) in 
          let z' = process_form hyps z ty in 
          let o' = process_form hyps o ty in 
          t_field (p',t',i',m',z',o',eq) (arg1,arg2) g
        else
          cannot_apply "field" "the eq doesn't coincide"
      | _ -> cannot_apply "field" "Think more about the goal")

let process_field_simp (p,t,i,m,z,o,e) g =
  let (hyps,concl) = get_goal g in
    (match concl.f_node with
      | Fapp(_,arg1 :: _) ->
        let ty = f_ty arg1 in
        let e' = process_form hyps e (tfun ty (tfun ty tbool)) in 
        let p' = process_form hyps p (tfun ty (tfun ty ty)) in 
        let t' = process_form hyps t (tfun ty (tfun ty ty)) in 
        let i' = process_form hyps i (tfun ty ty) in 
        let m' = process_form hyps m (tfun ty ty) in 
        let z' = process_form hyps z ty in 
        let o' = process_form hyps o ty in 
        t_field_simp (p',t',i',m',z',o',e') concl g
      | _ -> cannot_apply "field_simplify" "Think more about the goal")

(* -------------------------------------------------------------------- *)
let trans_pterm_argument hyps ue arg =
  let env = LDecl.toenv hyps in

  match unloc arg with
  | EA_form fp ->
      let fp = TT.transform_opt env ue fp None in
        Some (`Form fp)
      
  | EA_mem mem ->
      let mem = TT.transmem env mem in
        Some (`Memory mem)

  | EA_mp mp ->
      let (mp, mt) = TT.trans_msymbol env (mk_loc arg.pl_loc mp) in
        Some (`Module (mp, mt))

  | EA_none ->
      None

(* -------------------------------------------------------------------- *)
let rec destruct_product hyps fp =
  let module R = EcReduction in

  match EcFol.sform_of_form fp with
  | SFquant (Lforall, (x, t), f) -> Some (`Forall (x, t, f))
  | SFimp (f1, f2) -> Some (`Imp (f1, f2))
  | _ -> begin
    match R.h_red_opt R.full_red hyps fp with
    | None   -> None
    | Some f -> destruct_product hyps f
  end

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

  let ue  = EcUnify.UniEnv.create (Some (LDecl.tohyps hyps).h_tvar) in
  let tvi = omap tvi (TT.transtvi env ue) in

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
let process_pterm loc hyps pe =
  match pe.fp_kind with
  | FPNamed (fp, tyargs) ->
      process_named_pterm loc hyps (fp, tyargs)

  | FPCut fp ->
      let fp = process_form hyps fp tbool in
      let ue = EcUnify.UniEnv.create (Some (LDecl.tohyps hyps).h_tvar) in
        (`Cut fp, [], ue, fp)

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

  | Some (`Form tp),
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

  | Some (`Module (mp, mt)),
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
let process_apply loc pe g =
  let (hyps, fp) = (get_hyps g, get_concl g) in
  let (p, typs, ue, ax) = process_pterm loc hyps pe in
  let args = List.map (trans_pterm_argument hyps ue) pe.fp_args in
  let (ax, ids) = check_pterm_arguments hyps ue ax args in

  let rec instanciate (ax, ids) =
    let ev = evmap_of_pterm_arguments ids in

    try  (ax, ids, EcMetaProg.f_match hyps (ue, ev) ax fp);
    with MatchFailure ->
      match destruct_product hyps ax with
      | None   -> tacuerror "in apply, cannot find instance"
      | Some _ ->
          let (ax, id) = check_pterm_argument hyps ue ax None in
            instanciate (ax, id :: ids)
  in

  let (_, ids, (_, tue, ev)) =
    let fully_instantiate =
      can_concretize_pterm_arguments (ue, EV.empty) ids
    in

      match fully_instantiate with
      | false -> instanciate (ax, ids)
      | true  ->
          let closedax = Fsubst.uni (EcUnify.UniEnv.close ue) ax in

          if EcReduction.is_conv hyps closedax fp then begin
            (ax, ids, (ue, EcUnify.UniEnv.close ue, EV.empty))
          end else
            instanciate (ax, ids)
  in

  let args = concretize_pterm_arguments (tue, ev) ids in
  let typs = List.map (Tuni.subst tue) typs in

    match p with
    | `Global p ->
        gen_t_apply_glob (fun _ _ x -> x) p typs args g

    | `Local x -> 
        assert (typs = []);
        gen_t_apply_hyp (fun _ _ x -> x) x args g

    | `Cut fc ->
        assert (typs = []);
        gen_t_apply_form (fun _ _ x -> x)
          (Fsubst.uni (EcUnify.UniEnv.close ue) fc) args g

(* -------------------------------------------------------------------- *)
exception RwMatchFound of EcUnify.unienv * ty EcUidgen.Muid.t * form evmap

let process_rewrite1 loc ri g =
  match ri with
  | RWDone ->
      process_trivial g

  | RWRw (s, r, o, pe) ->
      let do1 g =
        let (hyps, concl) = get_goal g in

        let (p, typs, ue, ax) = process_pterm loc hyps pe in
        let args = List.map (trans_pterm_argument hyps ue) pe.fp_args in
        let ((_ax, ids), (_mode, (f1, f2))) =
          let rec find_rewrite_pattern (ax, ids) =
            match EcFol.sform_of_form ax with
            | EcFol.SFeq  (f1, f2) -> ((ax, ids), (`Eq, (f1, f2)))
            | EcFol.SFiff (f1, f2) -> ((ax, ids), (`Ev, (f1, f2)))
            | _ -> begin
              match destruct_product hyps ax with
              | None -> tacuerror "not an equation to rewrite"
              | Some _ ->
                  let (ax, id) = check_pterm_argument hyps ue ax None in
                    find_rewrite_pattern (ax, id :: ids)
            end
  
          in
            find_rewrite_pattern (check_pterm_arguments hyps ue ax args)
        in

        let fp = match s with `Normal -> f1 | `Reverse -> f2 in
  
        let (_ue, tue, ev) =
          let ev = evmap_of_pterm_arguments ids in
  
          let trymatch tp =
            try
              let (ue, tue, ev) = f_match hyps (ue, ev) ~ptn:fp tp in
                raise (RwMatchFound (ue, tue, ev))
            with MatchFailure -> false
          in
  
          try
            ignore (FPosition.select trymatch concl);
            tacuerror "cannot find an occurence for rewriting"
          with RwMatchFound (ue, tue, ev) -> (ue, tue, ev)
        in
  
        let args = concretize_pterm_arguments (tue, ev) ids in
        let typs = List.map (Tuni.subst tue) typs in
        let fp   = concretize_pterm (tue, ev) ids fp in

        let cpos =
          let test tp = EcReduction.is_alpha_eq hyps fp tp in
            FPosition.select test concl
        in

        assert (not (FPosition.is_empty cpos));

        let cpos =
          match o with
          | None   -> cpos
          | Some o ->
            let (min, max) = (Sint.min_elt o, Sint.max_elt o) in
              if min < 1 || max > FPosition.occurences cpos then
                tacuerror "invalid occurence selector";
              FPosition.filter o cpos
        in

        let fpat _ _ _ = FPosition.topattern cpos concl in

        match p with
        | `Global x ->
            t_rewrite_glob ~fpat s x typs args g
  
        | `Local x ->
            assert (typs = []);
            t_rewrite_hyp ~fpat s x args g
  
        | `Cut fc ->
            assert (typs = []);
            t_rewrite_form ~fpat s fc args g

      in
        match r with
        | None -> do1 g
        | Some (b, n) -> t_do b n do1 g

(* -------------------------------------------------------------------- *)
let process_rewrite loc ri g =
  set_loc loc (t_lseq (List.map (process_rewrite1 loc) ri)) g

(* -------------------------------------------------------------------- *)
let process_elim loc pe ((juc, n) as g) =
  let hyps = get_hyps g in

  let (p, typs, ue, ax) = process_pterm loc hyps pe in
  let args = List.map (trans_pterm_argument hyps ue) pe.fp_args in
  let (_ax, ids) = check_pterm_arguments hyps ue ax args in

  let (tue, ev) =
    if not (can_concretize_pterm_arguments (ue, EV.empty) ids) then
      tacuerror "in elim, cannot find instance";
    (EcUnify.UniEnv.close ue, EV.empty)
  in

  let args = concretize_pterm_arguments (tue, ev) ids in
  let typs = List.map (Tuni.subst tue) typs in

  let (juc, fn) =
    match p with
    | `Local  x -> mkn_hyp  juc hyps x
    | `Global x -> mkn_glob juc hyps x typs
    | `Cut    x -> new_goal juc (hyps, x)
  in

  let ((juc, an), gs) = mkn_apply (fun _ _ a -> a) (juc, fn) args in
  let (_, f) = get_node (juc, an) in

    t_on_first (t_use an gs) (set_loc loc (t_elim f) (juc, n))

(* -------------------------------------------------------------------- *)
let process_logic hitenv loc t =
  match t with
  | Passumption pq -> process_assumption loc pq
  | Psmt pi        -> process_smt hitenv pi
  | Pintro pi      -> process_intros pi
  | Psplit         -> t_split
  | Pfield st      -> process_field st
  | Pfieldsimp st  -> process_field_simp st
  | Pexists fs     -> process_exists fs
  | Pleft          -> t_left
  | Pright         -> t_right
  | Pcongr         -> process_congr
  | Ptrivial       -> process_trivial
  | Pelim pe       -> process_elim loc pe
  | Papply pe      -> process_apply loc pe
  | Pcut (name,phi)-> process_cut name phi
  | Pgeneralize l  -> process_generalize l
  | Pclear l       -> process_clear l
  | Prewrite ri    -> process_rewrite loc ri
  | Psubst   ri    -> process_subst loc ri
  | Psimplify ri   -> process_simplify ri
  | Pchange pf     -> process_change pf
  | PelimT i       -> process_elimT loc i
