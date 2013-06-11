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
open EcLogic
open EcPhl

module Sp = EcPath.Sp

module TT = EcTyping
module UE = EcUnify.UniEnv

(* -------------------------------------------------------------------- *)
type pprovers = EcParsetree.pprover_infos -> EcProvers.prover_infos

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
let process_tyargs env hyps tvi =
  let ue = EcUnify.UniEnv.create (Some hyps.h_tvar) in
    omap tvi (TT.transtvi env ue)

(* -------------------------------------------------------------------- *)
let process_instanciate env hyps ({pl_desc = pq; pl_loc = loc} ,tvi) =
  let (p, ax) =
    try EcEnv.Ax.lookup pq env
    with _ -> error loc (UnknownAxiom pq) in
  let args = process_tyargs env hyps tvi in
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
let process_global loc env tvi g =
  let hyps = get_hyps g in
  let p, tyargs = process_instanciate env hyps tvi in
  set_loc loc t_glob env p tyargs g

(* -------------------------------------------------------------------- *)
let process_assumption loc env (pq, tvi) g =
  let hyps,concl = get_goal g in
  match pq with
  | None ->
      if (tvi <> None) then error loc BadTyinstance;
      let h  =
        try find_in_hyps env concl hyps
        with _ -> assert false in
      t_hyp env h g
  | Some pq ->
      match unloc pq with
      | ([],ps) when LDecl.has_hyp ps hyps ->
          if (tvi <> None) then error pq.pl_loc BadTyinstance;
          set_loc loc (t_hyp env (fst (LDecl.lookup_hyp ps hyps))) g
      | _ -> process_global loc env (pq,tvi) g

(* -------------------------------------------------------------------- *)
let process_intros env pis =
  let mk_id s = EcIdent.create (odfl "_" s) in
    t_intros env (List.map (lmap mk_id) pis)

(* -------------------------------------------------------------------- *)
let process_elim_arg env hyps oty a =
  let ue  = EcUnify.UniEnv.create (Some hyps.h_tvar) in
  let env = tyenv_of_hyps env hyps in
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
let process_form_opt env hyps pf oty =
  let env = tyenv_of_hyps env hyps in
  let ue  = EcUnify.UniEnv.create (Some hyps.h_tvar) in
  let ff  = TT.transform_opt env ue pf oty in
  EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) ff

(* -------------------------------------------------------------------- *)
let process_form env hyps pf ty =
  process_form_opt env hyps pf (Some ty)

(* -------------------------------------------------------------------- *)
let process_formula env g pf =
  let hyps = get_hyps g in
    process_form env hyps pf tbool

(* -------------------------------------------------------------------- *)
let process_mkn_apply process_cut env pe (juc, _ as g) = 
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
        let p,tys = process_instanciate env hyps (pq,tvi) in
        mkn_glob env juc hyps p tys, []
      end
    | FPCut pf ->
      let f = process_cut env g pf in
      let juc, fn = new_goal juc (hyps, f) in
      (juc,fn), [fn]
  in
  let (juc,an), ags = mkn_apply process_elim_arg env (juc,fn) args in
  (juc,an), fgs@ags

(* -------------------------------------------------------------------- *)
let process_apply loc env pe (_,n as g) =
  let (juc, an), gs = process_mkn_apply process_formula env pe g in
    try
      set_loc loc (t_use env an gs) (juc,n)
    with tope ->
      let (_, tp) = (get_node (juc, n)) in

      let rec doit ids fp =
        let (x, gty, fp) =
          match is_forall fp with
          | true  -> destr_forall1 fp
          | false -> raise tope
        in

        let ty = match gty with GTty ty -> ty | _ -> raise tope in

        try
          let ev = EV.of_idents (List.map fst ((x, ty) :: ids)) in
          let _, _, ev =
            EcMetaProg.f_match (env, get_hyps g) (EcUnify.UniEnv.create None, ev) ~ptn:fp tp
          in

          let (s, ras) =
            List.map_fold
              (fun s (x, xty) ->
                 let xf = EV.doget x ev in
                   EcReduction.check_type env xty xf.f_ty;
                   (f_bind_local s x xf, RA_form xf))
              f_subst_id (List.rev ((x, ty) :: ids))
          in

          let concl     = f_subst s fp in
          let (juc, n1) = new_goal juc (get_hyps g, concl) in
          let rule      = { pr_name = RN_apply; pr_hyps = RA_node an :: ras } in
          let juc, _    = upd_rule rule (juc, n1) in
          let ns        = List.pmap (function RA_node n -> Some n | _ -> None) ras in

            (set_loc loc (t_use env n1 (gs @ ns))) (juc, n)

        with MatchFailure ->
          doit ((x, ty) :: ids) fp

      in
        doit [] (snd (get_node (juc, an)))

(* -------------------------------------------------------------------- *)
let process_elim loc env pe (_,n as g) =
  let (juc,an), gs = process_mkn_apply process_formula env pe g in
  let (_,f) = get_node (juc, an) in
  t_on_first (set_loc loc (t_elim env f) (juc,n)) (t_use env an gs)

(* -------------------------------------------------------------------- *)
let process_rewrite loc env (s,pe) (_,n as g) =
  set_loc loc (t_rewrite_node env 
                 (process_mkn_apply process_formula env pe g) s) n

(* -------------------------------------------------------------------- *)
let process_trivial mkpv pi env g =
  let pi = mkpv pi in
  t_seq (t_simplify_nodelta env) (t_trivial pi env) g

(* -------------------------------------------------------------------- *)
let process_cut name env phi g =
  let phi = process_formula env g phi in
  t_on_last (t_cut env phi g)
    (process_intros env [lmap (fun x -> Some x) name])

(* -------------------------------------------------------------------- *)
let process_generalize env l =
  let pr1 pf g =
    let hyps = get_hyps g in
    match pf.pl_desc with
    | PFident({pl_desc = ([],s)},None) when LDecl.has_symbol s hyps ->
      let id = fst (LDecl.lookup s hyps) in
      t_generalize_hyp env id g
    | _ ->
      let f = process_form_opt env hyps pf None in
      t_generalize_form None env f g in
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
let process_exists env fs g =
  gen_t_exists process_elim_arg env fs g

(* -------------------------------------------------------------------- *)
let process_change env pf g =
  let f = process_formula env g pf in
  set_loc pf.pl_loc (t_change env f) g

(* -------------------------------------------------------------------- *)
let process_simplify env ri g =
  let hyps = get_hyps g in
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
  t_simplify env ri g

(* -------------------------------------------------------------------- *)
let process_elimT loc env (pf,qs) g =
  let p = set_loc qs.pl_loc (EcEnv.Ax.lookup_path qs.pl_desc) env in
  let f = process_form_opt env (get_hyps g) pf None in
  t_seq (set_loc loc (t_elimT env f p))
    (t_simplify env EcReduction.beta_red) g

(* -------------------------------------------------------------------- *)
let process_subst loc env ri g =
  if ri = [] then t_subst_all env g
  else
    let hyps = get_hyps g in
    let totac ps =
      let f = process_form_opt env hyps ps None in
      try t_subst1 env (Some f) 
      with _ -> assert false (* FIXME error message *) in
    let tacs = List.map totac ri in
    set_loc loc (t_lseq tacs) g

(* -------------------------------------------------------------------- *)
let process_field (p,t,i,m,z,o,e) env g =
  let (hyps,concl) = get_goal g in
    (match concl.f_node with
      | Fapp(eq',[arg1;arg2]) ->
        let ty = f_ty arg1 in
        let eq = process_form env hyps e (tfun ty (tfun ty tbool)) in
        if (f_equal eq eq' ) then
          let p' = process_form env hyps p (tfun ty (tfun ty ty)) in 
          let t' = process_form env hyps t (tfun ty (tfun ty ty)) in 
          let i' = process_form env hyps i (tfun ty ty) in 
          let m' = process_form env hyps m (tfun ty ty) in 
          let z' = process_form env hyps z ty in 
          let o' = process_form env hyps o ty in 
          t_field (p',t',i',m',z',o',eq) (arg1,arg2) g
        else
          cannot_apply "field" "the eq doesn't coincide"
      | _ -> cannot_apply "field" "Think more about the goal")

let process_field_simp (p,t,i,m,z,o,e) env g =
  let (hyps,concl) = get_goal g in
    (match concl.f_node with
      | Fapp(_,arg1 :: _) ->
        let ty = f_ty arg1 in
        let e' = process_form env hyps e (tfun ty (tfun ty tbool)) in 
        let p' = process_form env hyps p (tfun ty (tfun ty ty)) in 
        let t' = process_form env hyps t (tfun ty (tfun ty ty)) in 
        let i' = process_form env hyps i (tfun ty ty) in 
        let m' = process_form env hyps m (tfun ty ty) in 
        let z' = process_form env hyps z ty in 
        let o' = process_form env hyps o ty in 
        t_field_simp (p',t',i',m',z',o',e') concl g
      | _ -> cannot_apply "field_simplify" "Think more about the goal")

(* -------------------------------------------------------------------- *)
let trans_apply_arg (env, hyps) ue arg =
  let env = tyenv_of_hyps env hyps in

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
let rec destruct_product (env, hyps) fp =
  let module P = EcPath      in
  let module C = EcCoreLib   in
  let module R = EcReduction in

  match fp.f_node with
  | Fapp ({f_node = Fop(p, _)}, [f1; f2]) when P.p_equal p C.p_imp ->
      Some (`Imp (f1, f2))

  | Fquant (Lforall, (x, t) :: bd, f) ->
      Some (`Forall (x, t, EcFol.f_forall bd f))

  | _ -> begin
    match R.h_red_opt R.full_red env hyps fp with
    | None   -> None
    | Some f -> destruct_product (env, hyps) f
  end

(* -------------------------------------------------------------------- *)
let process_named_apply _loc (env, hyps) (fp, tvi) =
  let env = tyenv_of_hyps env hyps in

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

  let ue  = EcUnify.UniEnv.create (Some hyps.h_tvar) in
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
let process_new_apply loc env pe g =
  let (hyps, fp) = (get_hyps g, get_concl g) in
  let lenv = tyenv_of_hyps env hyps in

  let (p, typarams, ue, ax) =
    match pe.fp_kind with
    | FPNamed (fp, tyargs) ->
        process_named_apply loc (env, hyps) (fp, tyargs)

    | FPCut fp ->
        let fp = process_formula env g fp in
        let ue = EcUnify.UniEnv.create (Some hyps.h_tvar) in
          (`Cut fp, [], ue, fp)
  in

  let args = pe.fp_args in
  let args = List.map (trans_apply_arg (env, hyps) ue) args in

  let check_arg f arg =
    let invalid_arg () = tacuerror "invalid argument to apply" in

    match arg, destruct_product (env, hyps) f with
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
          EcUnify.unify lenv ue tp.f_ty ty;
          (EcFol.f_subst_local x tp f, `KnownVar (x, tp))
        with EcUnify.UnificationFailure _ ->
          invalid_arg ()
    end

    | Some (`Memory m),
      Some (`Forall (x, GTmem _, f)) ->
        (EcFol.f_subst_mem x m f, `KnownMem (x, m))

    | Some (`Module (mp, mt)),
      Some (`Forall (x, GTmodty (emt, restr), f)) ->
        check_modtype_restr env mp mt emt restr;
        (EcFol.f_subst_mod x mp f, `KnownMod (x, (mp, mt)))

    | _, _ -> invalid_arg ()

  in

  let rec instanciate (ax, ids) =
    let ev =
      let forid id ev =
        match id with
        | `UnknownVar (x, _) -> EV.add x ev
        | _ -> ev
      in
        List.fold_right forid ids EV.empty
    in
      try  (ax, ids, EcMetaProg.f_match (env, hyps) (ue, ev) ax fp);
      with MatchFailure ->
        match destruct_product (env, hyps) ax with
        | None   -> tacuerror "in apply, cannot find instance"
        | Some _ ->
            let (ax, id) = check_arg ax None in
              instanciate (ax, id :: ids)
  in

  let (ax, ids) = sndmap List.rev (List.map_fold check_arg ax args) in

  let (_, ids, (_, tue, ev)) =
    let is_not_fully_instantiate =
         not (EcUnify.UniEnv.closed ue)
      || List.exists (function `UnknowVar _ -> true | _ -> false) ids
    in
      match is_not_fully_instantiate with
      | true  -> instanciate (ax, ids)
      | false ->
          let closedax = Fsubst.uni (EcUnify.UniEnv.close ue) ax in

          if EcReduction.is_conv lenv hyps closedax fp then begin
            (ax, ids, (ue, EcUnify.UniEnv.close ue, EV.empty))
          end else
            instanciate (ax, ids)
  in

  let args =
    let do1 = function
      | `KnownMod   (_, (mp, mt)) -> EcLogic.AAmp   (mp, mt)
      | `KnownMem   (_, mem)      -> EcLogic.AAmem  mem
      | `KnownVar   (_, tp)       -> EcLogic.AAform (Fsubst.uni tue tp)
      | `SideCond   _             -> EcLogic.AAnode
      | `UnknownVar (x, _)        -> EcLogic.AAform (Fsubst.uni tue (EV.doget x ev))
    in
      List.rev (List.map do1 ids)
  in

  let typarams = List.map (Tuni.subst tue) typarams in

    match p with
    | `Global p ->
          gen_t_apply_glob (fun _ _ _ x -> x) env p typarams args g

    | `Local  x -> 
        assert (typarams = []);
        gen_t_apply_hyp (fun _ _ _ x -> x) env x args g

    | `Cut fc ->
        assert (typarams = []);
        gen_t_apply_form (fun _ _ _ x -> x) env
          (Fsubst.uni (EcUnify.UniEnv.close ue) fc) args g

(* -------------------------------------------------------------------- *)
let process_logic mkpv loc env t =
  match t with
  | Passumption pq -> process_assumption loc env pq
  | Ptrivial pi    -> process_trivial mkpv pi env
  | Pintro pi      -> process_intros env pi
  | Psplit         -> t_split env
  | Pfield st      -> process_field st env
  | Pfieldsimp st  -> process_field_simp st env 
  | Pexists fs     -> process_exists env fs
  | Pleft          -> t_left env
  | Pright         -> t_right env
  | Pelim pe       -> process_elim  loc env pe
  | Papply pe      -> process_new_apply loc env pe
  | Pcut (name,phi)-> process_cut name env phi
  | Pgeneralize l  -> process_generalize env l
  | Pclear l       -> process_clear l
  | Prewrite ri    -> process_rewrite loc env ri
  | Psubst   ri    -> process_subst loc env ri
  | Psimplify ri   -> process_simplify env ri
  | Pchange pf     -> process_change env pf
  | PelimT i       -> process_elimT loc env i
