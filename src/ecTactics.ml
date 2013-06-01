(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcLocation
open EcSymbols
open EcParsetree
open EcTypes
open EcModules
open EcFol

open EcBaseLogic
open EcLogic
open EcPhl

module Sp = EcPath.Sp

module TT = EcTyping
module UE = EcUnify.UniEnv

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

let process_tyargs env hyps tvi =
  let ue = EcUnify.UniEnv.create (Some hyps.h_tvar) in
    omap tvi (TT.transtvi env ue)

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

let process_global loc env tvi g =
  let hyps = get_hyps g in
  let p, tyargs = process_instanciate env hyps tvi in
  set_loc loc t_glob env p tyargs g

let process_assumption loc env (pq,tvi) g =
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

let process_intros env pis =
  let mk_id s = EcIdent.create (odfl "_" s) in
    t_intros env (List.map (lmap mk_id) pis)

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

let process_form_opt env hyps pf oty =
  let env = tyenv_of_hyps env hyps in
  let ue  = EcUnify.UniEnv.create (Some hyps.h_tvar) in
  let ff  = TT.transform_opt env ue pf oty in
  EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) ff

let process_form env hyps pf ty =
  process_form_opt env hyps pf (Some ty)

let process_formula env g pf =
  let hyps = get_hyps g in
  process_form env hyps pf tbool

let process_phl_form ty env g phi =
  let hyps, concl = get_goal g in
  let m = 
    try 
      let hs = set_loc phi.pl_loc destr_hoareS concl in
      hs.hs_m
    with _ ->
      let hs = set_loc phi.pl_loc destr_bdHoareS concl in
      hs.bhs_m
  in
  let env = EcEnv.Memory.push_active m env in
  process_form env hyps phi ty

let process_prhl_form ty env g phi =
  let hyps, concl = get_goal g in
  let es = set_loc phi.pl_loc destr_equivS concl in
  let env = EcEnv.Memory.push_all [es.es_ml; es.es_mr] env in
  process_form env hyps phi ty

let process_phl_formula = process_phl_form tbool

let process_prhl_formula = process_prhl_form tbool
    
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

let process_apply loc env pe (_,n as g) =
  let (juc,an), gs = process_mkn_apply process_formula env pe g in
  set_loc loc (t_use env an gs) (juc,n)

let process_elim loc env pe (_,n as g) =
  let (juc,an), gs = process_mkn_apply process_formula env pe g in
  let (_,f) = get_node (juc, an) in
  t_on_first (set_loc loc (t_elim env f) (juc,n)) (t_use env an gs)

let process_rewrite loc env (s,pe) (_,n as g) =
  set_loc loc (t_rewrite_node env 
                 (process_mkn_apply process_formula env pe g) s) n

let process_trivial mkpv pi env g =
  let pi = mkpv pi in
  t_trivial pi env g

let process_cut name env phi g =
  let phi = process_formula env g phi in
  t_on_last (t_cut env phi g)
    (process_intros env [lmap (fun x -> Some x) name])

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

let process_clear l g =
  let hyps = get_hyps g in
  let toid ps =
    let s = ps.pl_desc in
    if LDecl.has_symbol s hyps then (fst (LDecl.lookup s hyps))
    else error ps.pl_loc (UnknownHypSymbol s) in
  let ids = EcIdent.Sid.of_list (List.map toid l) in
  t_clear ids g

let process_exists env fs g =
  gen_t_exists process_elim_arg env fs g

let process_change env pf g =
  let f = process_formula env g pf in
  set_loc pf.pl_loc (t_change env f) g

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

let process_elimT loc env (pf,qs) g =
  let p = set_loc qs.pl_loc (EcEnv.Ax.lookup_path qs.pl_desc) env in
  let f = process_form_opt env (get_hyps g) pf None in
  t_seq (set_loc loc (t_elimT env f p))
    (t_simplify env EcReduction.beta_red) g

let process_case loc env pf g =
  let concl = get_concl g in
  match concl.f_node with
  | FhoareS _ ->
    let f = process_phl_formula env g pf in
    t_hoare_case f g
  | FequivS _ ->
    let f = process_prhl_formula env g pf in
    t_equiv_case f g
  | _ ->
    let f = process_formula env g pf in
    t_seq (set_loc loc (t_case env f))
      (t_simplify env EcReduction.betaiota_red) g

let process_subst loc env ri g =
  if ri = [] then t_subst_all env g
  else
    let hyps = get_hyps g in
    let totac ps =
      let s = ps.pl_desc in
      try t_subst1 env (Some (fst (LDecl.lookup_var s hyps)))
      with _ -> error ps.pl_loc (UnknownHypSymbol s) in
    let tacs = List.map totac ri in
    set_loc loc (t_lseq tacs) g

let process_app env dir k phi bd_opt g =
  let concl = get_concl g in
  match k, bd_opt with
    | Single i, None when is_hoareS concl ->
      let phi = process_phl_formula env g phi in
      t_hoare_app i phi g
    | Single i, _ when is_bdHoareS concl ->
      let phi = process_phl_formula env g phi in
      let bd_opt = omap bd_opt (process_phl_form treal env g) in
      t_bdHoare_app dir i phi bd_opt g
    | Double(i,j), None ->
      let phi = process_prhl_formula env g phi in
      t_equiv_app (i,j) phi g
    | Single _, None ->
      cannot_apply "app" "wrong position parameter"
    | _, Some _ ->
      cannot_apply "app" "optional bound parameter not supported"

let process_while env phi vrnt_opt info g =
  let concl = get_concl g in
  if is_hoareS concl then
    match vrnt_opt,info with
      | None, None ->
        t_hoare_while env (process_phl_formula env g phi) g
      | _ -> cannot_apply "while" "wrong arguments"
  else if is_bdHoareS concl then
    match vrnt_opt,info with
      | Some vrnt, info ->
        t_bdHoare_while env 
          (process_phl_formula env g phi) 
          (process_phl_form tint env g vrnt) 
          (omap info (fun (bd,i) -> process_phl_form treal env g bd,
            process_phl_form tint env g i))
          g
      | _ -> cannot_apply "while" "wrong arguments"
  else if is_equivS concl then
    match vrnt_opt,info with
      | None, None ->
        t_equiv_while env (process_prhl_formula env g phi) g
      | _ -> cannot_apply "while" "wrong arguments"
  else cannot_apply "while" "the conclusion is not a hoare or a equiv"

let process_fission env (side, cpos, infos) g =
  t_fission env side cpos infos g

let process_fusion env (side, cpos, infos) g =
  t_fusion env side cpos infos g

let process_unroll env (side, cpos) g =
  t_unroll env side cpos g


let process_exp env hyps e oty =
  let env = tyenv_of_hyps env hyps in
  let ue  = EcUnify.UniEnv.create (Some hyps.h_tvar) in
  TT.transexpcast env ue oty e
  (* Some substitution like 
        EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) e 
     is missing?
  *)
let process_phl_exp env g e ty = 
  let hyps, concl = get_goal g in
  let m = 
    try 
      let hs = set_loc e.pl_loc destr_hoareS concl in
      hs.hs_m
    with _ ->
      let hs = set_loc e.pl_loc destr_bdHoareS concl in
      hs.bhs_m
  in
  let env = EcEnv.Memory.push_active m env in
  process_exp env hyps e ty

let process_splitwhile env (b, side, cpos) g =
  let b = process_phl_exp env g b tbool in
  t_splitwhile b env side cpos g

let process_call env side pre post g =
  let hyps,concl = get_goal g in
  match concl.f_node, side with
  | FhoareS hs, None ->
    let (_,f,_),_ = s_last_call "call" hs.hs_s in
    let penv, qenv = EcEnv.Fun.hoareF f env in
    let pre  = process_form penv hyps pre tbool in
    let post = process_form qenv hyps post tbool in
    t_hoare_call env pre post g
  | FhoareS _, Some _ ->
    cannot_apply "call" "side can only be given for prhl judgements"
  | FequivS es, None ->
    let (_,fl,_),(_,fr,_),_,_ = s_last_calls "call" es.es_sl es.es_sr in
    let env' = tyenv_of_hyps env hyps in
    let penv, qenv = EcEnv.Fun.equivF fl fr env' in
    let pre  = process_form penv hyps pre tbool in
    let post = process_form qenv hyps post tbool in
    t_equiv_call env pre post g
  | FequivS es, Some side ->
    let fstmt = match side with true -> es.es_sl | false -> es.es_sr in
    let (_,f,_),_ = s_last_call "call" fstmt in
    let penv, qenv = EcEnv.Fun.hoareF f env in
    let pre  = process_form penv hyps pre tbool in
    let post = process_form qenv hyps post tbool in
    t_equiv_call1 env side pre post g
  | _ -> cannot_apply "call" "the conclusion is not a hoare or a equiv"

let process_cond env side g =
  let concl = get_concl g in
  if is_equivS concl then
    t_equiv_cond env side g
  else if is_hoareS concl || is_bdHoareS concl then
    match side with
      | Some _ -> cannot_apply "cond" "Unexpected side in non relational goal"
      | None ->
        if is_hoareS concl then t_hoare_cond env g else t_bdHoare_cond env g
  else cannot_apply "cond" "the conclusion is not a hoare or a equiv goal"

let rec process_swap1 env info g =
  let side,pos = info.pl_desc in
  match side with
  | None ->
    t_seq (process_swap1 env {info with pl_desc = (Some true, pos)})
      (process_swap1 env {info with pl_desc = (Some false, pos)}) g
  | Some side ->
    let tac =
      match pos with
      | SKbase(p1,p2,p3) -> t_equiv_swap env side p1 p2 p3
      | SKmove p ->
        if 0 < p then t_equiv_swap env side 1 2 (p+1)
        else if p < 0 then
          let concl = get_concl g in
          let es = set_loc info.pl_loc destr_equivS concl in
          let s = if side then es.es_sl else es.es_sr in
          let len = List.length s.s_node in
          t_equiv_swap env side (len+p) len len
        else (* p = 0 *) t_id None
      | SKmovei(i,p) ->
        if 0 < p then t_equiv_swap env side i (i+1) (i+p)
        else if p < 0 then t_equiv_swap env side (i+p) i i
        else (* p = 0 *) t_id None
      | SKmoveinter(i1,i2,p) ->
        if 0 < p then t_equiv_swap env side i1 (i2+1) (i2+p)
        else if p < 0 then t_equiv_swap env side (i1+p) i1 i2
        else (* p = 0 *) t_id None
    in
    set_loc info.pl_loc tac g

let process_swap env info =
  t_lseq (List.map (process_swap1 env) info)

(* TODO move this *)
let pat_all fs s =
  let rec aux_i i = 
    match i.i_node with
    | Scall(_,f,_) -> 
      if EcPath.Sx.mem f fs then Some IPpat else None
    | Sif(_,s1,s2) -> 
      let sp1 = aux_s 0 s1.s_node in
      let sp2 = aux_s 0 s2.s_node in
      if sp1 = [] && sp2 = [] then None 
      else Some (IPif(sp1,sp2))
    | Swhile(_,s) ->
      let sp = aux_s 0 s.s_node in
      if sp = [] then None else Some (IPwhile(sp)) 
    | _ -> None
  and aux_s n s = 
    match s with
    | [] -> []
    | i::s ->
      match aux_i i with
      | Some ip -> (n,ip) :: aux_s 0 s 
      | None -> aux_s (n+1) s in
  aux_s 0 s.s_node
  
let rec process_inline_all env side fs g =
  let concl = get_concl g in
  match concl.f_node, side with
  | FequivS _, None ->
      t_seq
        (process_inline_all env (Some true ) fs)
        (process_inline_all env (Some false) fs) g
  | FequivS es, Some b ->
      let sp = pat_all fs (if b then es.es_sl else es.es_sr) in
        if   sp = []
        then t_id None g
        else t_seq
               (t_inline_equiv env b sp)
               (process_inline_all env side fs) g
  | FhoareS hs, None ->
      let sp = pat_all fs hs.hs_s in
        if   sp = []
        then t_id None g
        else t_seq
               (t_inline_hoare env sp)
               (process_inline_all env side fs) g

  | _, _ -> assert false (* FIXME error message *)
  
let pat_of_occs cond occs s =
  let occs = ref occs in
  let rec aux_i occ i = 
    match i.i_node with
    | Scall (_,f,_) -> 
      if cond f then 
        let occ = 1 + occ in
        if Sint.mem occ !occs then begin
          occs := Sint.remove occ !occs; 
          occ, Some IPpat
        end else occ, None
      else occ, None
    | Sif(_,s1,s2) ->
      let occ, sp1 = aux_s occ 0 s1.s_node in
      let occ, sp2 = aux_s occ 0 s2.s_node in
      let ip = if sp1 = [] && sp2 = [] then None else Some(IPif(sp1,sp2)) in
      occ, ip
    | Swhile(_,s) ->
      let occ, sp = aux_s occ 0 s.s_node in
      let ip = if sp = [] then None else Some(IPwhile sp) in
      occ, ip
    | _ -> occ, None 
  and aux_s occ n s =
    match s with
    | [] -> occ, []
    | i::s ->
      match aux_i occ i with
      | occ, Some ip -> 
        let occ, sp = aux_s occ 0 s in
        occ, (n,ip) :: sp
      | occ, None -> aux_s occ (n+1) s in
  let _, sp = aux_s 0 0 s.s_node in
  assert (Sint.is_empty !occs); (* FIXME error message *)
  sp

let process_inline_occs env side fs occs g =
  let cond = 
    if EcPath.Sx.is_empty fs then fun _ -> true
    else fun f -> EcPath.Sx.mem f fs in
  let occs = Sint.of_list occs in
  let concl = get_concl g in
  match concl.f_node, side with
  | FequivS es, Some b ->
    let sp =  pat_of_occs cond occs (if b then es.es_sl else es.es_sr) in
    t_inline_equiv env b sp g 
  | FhoareS hs, None ->
    let sp =  pat_of_occs cond occs hs.hs_s in
    t_inline_hoare env sp g 
  | _, _ -> assert false (* FIXME error message *)
  

let process_inline env infos g =
  match infos with
  | `ByName (side, (fs, occs)) -> begin
      let hyps = get_hyps g in
      let env' = tyenv_of_hyps env hyps in
      let fs = 
        List.fold_left (fun fs f ->
          let f = EcTyping.trans_gamepath env' f in
          EcPath.Sx.add f fs) EcPath.Sx.empty fs 
      in
      match occs with
      | None -> process_inline_all env side fs g
      | Some occs -> process_inline_occs env side fs occs g
    end

  | `ByPattern _ -> failwith "not-implemented"

let process_alias env (side, cpos, id) g =
  t_alias env side cpos id g

let process_rnd side env tac_info g =
  let concl = get_concl g in
  match side, tac_info with 
    | None, (None, None) when is_hoareS concl -> t_hoare_rnd env g
    | None, (opt_bd, opt_event) when is_bdHoareS concl ->
      let opt_bd = omap opt_bd (process_phl_form treal env g)  in
      let event ty = omap opt_event (process_phl_form (tfun ty tbool) env g) in
      t_bd_hoare_rnd env (opt_bd,event) g
    | _ when is_equivS concl ->
      let process_form f ty1 ty2 = process_prhl_form (tfun ty1 ty2) env g f in
      let bij_info = match tac_info with
        | None,None -> None, None
        | Some f, None | None, Some f -> Some (process_form f), None
        | Some f, Some finv -> Some (process_form f), Some (process_form finv)
      in
      t_equiv_rnd side env bij_info g
    | _ -> cannot_apply "rnd" "unexpected instruction or wrong arguments"

let process_equiv_deno env info (_,n as g) = 
  let process_cut env g (pre,post) = 
    let hyps,concl = get_goal g in
    let _op, f1, f2 =
      match concl.f_node with
      | Fapp({f_node = Fop(op,_)}, [f1;f2]) when is_pr f1 && is_pr f2 -> 
        op, f1, f2
      | _ -> cannot_apply "equiv_deno" "" in (* FIXME error message *) 
    let _,fl,_,_ = destr_pr f1 in
    let _,fr,_,_ = destr_pr f2 in
    let penv, qenv = EcEnv.Fun.equivF fl fr env in
    let pre  = omap_dfl pre  f_true (fun p -> process_form penv hyps p tbool) in
    let post = omap_dfl post f_true (fun p -> process_form qenv hyps p tbool) in
    f_equivF pre fl fr post in
  let (juc,an), gs = process_mkn_apply process_cut env info g in
  let pre,post =
    let (_,f) = get_node (juc,an) in
    let ef = destr_equivF f in
    ef.ef_pr, ef.ef_po in
  t_on_first (t_equiv_deno env pre post (juc,n)) (t_use env an gs)

let process_conseq env info (_, n as g) =
  let t_pre = ref (t_id None) and t_post = ref (t_id None) in
  let tac1 g =
    let hyps = get_hyps g in
    let m, h = match LDecl.fresh_ids hyps ["&m";"H"] with
      | [m;h] -> m,h
      | _ -> assert false in
    t_seq (t_intros_i env [m;h]) (t_hyp env h) g in
  let tac2 g =
    let hyps = get_hyps g in
    let m1,m2, h = match LDecl.fresh_ids hyps ["&m";"&m";"H"] with
      | [m1;m2;h] -> m1,m2,h
      | _ -> assert false in
    t_seq (t_intros_i env [m1;m2;h]) (t_hyp env h) g in
  let process_cut env g (pre,post) =
    let hyps,concl = get_goal g in        
    let tac, penv, qenv, gpre, gpost, fmake = 
      match concl.f_node with
      | FhoareF hf ->
        let penv, qenv = EcEnv.Fun.hoareF hf.hf_f env in
        tac1, penv, qenv, hf.hf_pr, hf.hf_po, 
        (fun pre post -> f_hoareF pre hf.hf_f post)
      | FhoareS hs ->
        let env = EcEnv.Memory.push_active hs.hs_m env in
        tac1, env, env, hs.hs_pr, hs.hs_po,
        (fun pre post -> f_hoareS_r { hs with hs_pr = pre; hs_po = post })
      | FequivF ef ->
        let penv, qenv = EcEnv.Fun.equivF ef.ef_fl ef.ef_fr env in
        tac2, penv, qenv, ef.ef_pr, ef.ef_po,
        (fun pre post -> f_equivF pre ef.ef_fl ef.ef_fr post)
      | FequivS es -> 
        let env = EcEnv.Memory.push_all [es.es_ml; es.es_mr] env in
        tac2, env, env, es.es_pr, es.es_po,
        (fun pre post -> f_equivS_r { es with es_pr = pre; es_po = post }) 
      | _ -> assert false (* FIXME error message *)
    in
    let pre = match pre with
      | None -> t_pre := tac; gpre 
      | Some pre ->  process_form penv hyps pre tbool in
    let post = match post with
      | None -> t_post := tac; gpost 
      | Some post ->  process_form qenv hyps post tbool in
    fmake pre post in
  let (juc,an), gs = process_mkn_apply process_cut env info g in
  let t_conseq = 
    let (_,f) = get_node (juc,an) in
    match f.f_node with
    | FhoareF hf -> t_hoareF_conseq env hf.hf_pr hf.hf_po
    | FhoareS hs -> t_hoareS_conseq env hs.hs_pr hs.hs_po
    | FequivF ef -> t_equivF_conseq env ef.ef_pr ef.ef_po
    | FequivS es -> t_equivS_conseq env es.es_pr es.es_po 
    | _ -> assert false (* FIXME error message *) in
  t_seq_subgoal t_conseq
    [!t_pre; !t_post; t_use env an gs] (juc,n)
  
let process_fun_abs env inv g =
  let env' = EcEnv.Fun.inv_memenv env in
  let inv = process_formula env' g inv in
  t_equivF_abs env inv g
  
let process_fun_upto env (bad, p, o) g =
  let env' = EcEnv.Fun.inv_memenv env in 
  let p = process_formula env' g p in
  let q = 
    match o with
    | None -> EcFol.f_true
    | Some q -> process_formula env' g q in
  let bad = 
    let env =  EcEnv.Memory.push_active (EcFol.mhr,None) env in
    process_formula env g bad in
  t_equivF_abs_upto env bad p q g
    
let process_phl loc env ptac g =
  let t =
    match ptac with
    | Pfun_def -> EcPhl.t_fun_def env
    | Pfun_abs f -> process_fun_abs env f
    | Pfun_upto info -> process_fun_upto env info 
    | Pskip    -> EcPhl.t_skip
    | Papp (dir,k,phi,f) -> process_app env dir k phi f
    | Pwp  k   -> t_wp env k
    | Prcond (side,b,i) -> t_rcond side b i
    | Pcond side   -> process_cond env side
    | Pwhile (phi,vrnt_opt,info) -> process_while env phi vrnt_opt info
    | Pfission info -> process_fission env info
    | Pfusion info -> process_fusion env info
    | Punroll info -> process_unroll env info
    | Psplitwhile info -> process_splitwhile env info
    | Pcall(side, (pre, post)) -> process_call env side pre post
    | Pswap info -> process_swap env info
    | Pinline info -> process_inline env info
    | Palias info -> process_alias env info
    | Prnd (side,info) -> process_rnd side env info
    | Pconseq info -> process_conseq env info
    | Pequivdeno info -> process_equiv_deno env info
  in
  set_loc loc t g

let process_debug env =
  let l = fun x -> EcLocation.mk_loc EcLocation._dummy x in
  let (p, _) = EcTyping.trans_msymbol env (l [(l "M", Some [l [(l "K", None)]])]) in
    ignore (EcEnv.Mod.by_mpath p env)

let rec process_logic_tacs mkpv env (tacs:ptactics) (gs:goals) : goals =
  match tacs with
  | [] -> gs
  | {pl_desc = Psubgoal tacs1; pl_loc = loc } :: tacs2 ->
      let gs =
        set_loc loc
          (t_subgoal (List.map (process_logic_tac mkpv env) tacs1)) gs in
      process_logic_tacs mkpv env tacs2 gs
  | tac1 :: tacs2 ->
      let gs = t_on_goals (process_logic_tac mkpv env tac1) gs in
      process_logic_tacs mkpv env tacs2 gs

and process_logic_tac mkpv env (tac:ptactic) (g:goal) : goals =
  let loc = tac.pl_loc in
  let tac =
    match unloc tac with
    | Pidtac msg     -> t_id msg
    | Prepeat t      -> t_repeat (process_logic_tac mkpv env t)
    | Pdo (None,t)   -> 
      let tac = (process_logic_tac mkpv env t) in
      t_seq tac (t_repeat tac)
    | Pdo (Some i, t) -> t_do i (process_logic_tac mkpv env t)
    | Ptry t         -> t_try (process_logic_tac mkpv env t)
    | Passumption pq -> process_assumption loc env pq
    | Ptrivial pi    -> process_trivial mkpv pi env
    | Pintro pi      -> process_intros env pi
    | Psplit         -> t_split env
    | Pexists fs     -> process_exists env fs
    | Pleft          -> t_left env
    | Pright         -> t_right env
    | Pelim pe       -> process_elim  loc env pe
    | Papply pe      -> process_apply loc env pe
    | Pcut (name,phi)-> process_cut name env phi
    | Pgeneralize l  -> process_generalize env l
    | Pclear l       -> process_clear l
    | Prewrite ri    -> process_rewrite loc env ri
    | Psubst   ri    -> process_subst loc env ri
    | Psimplify ri   -> process_simplify env ri
    | Pchange pf     -> process_change env pf
    | PelimT i       -> process_elimT loc env i
    | Pcase  i       -> process_case  loc env i
    | Pseq tacs      ->
        fun (juc,n) -> process_logic_tacs mkpv env tacs (juc,[n])
    | Psubgoal _     -> assert false

    | Padmit         -> t_admit
    | Pdebug         -> process_debug env; t_id None

    | PPhl tac       -> process_phl loc env tac
  in
  set_loc loc tac g

