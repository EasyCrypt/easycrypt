(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcParsetree
open EcLocation
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcReduction
open EcBaseLogic
open EcLogic
open EcHiLogic
open EcCorePhl
open EcCoreHiPhl
open EcCoreHiLogic
open EcPhl

module TT = EcTyping
module UE = EcUnify.UniEnv

(* -------------------------------------------------------------------- *)
let process_while side_opt phi vrnt_opt g =
  let concl = get_concl g in
  if is_hoareS concl then
    match vrnt_opt with
      | None ->
        t_hoare_while (process_phl_formula g phi) g
      | _ -> cannot_apply "while" "wrong arguments"
  else if is_bdHoareS concl then
    match vrnt_opt with
      | Some vrnt ->
        t_bdHoare_while 
          (process_phl_formula g phi) 
          (process_phl_form tint g vrnt) 
          g
      | _ -> cannot_apply "while" "wrong arguments"
  else if is_equivS concl then
    match side_opt, vrnt_opt with
      | None, None ->
        t_equiv_while (process_prhl_formula g phi) g
      | Some side, Some vrnt ->
        t_equiv_while_disj side (process_prhl_form tint g vrnt) (process_prhl_formula g phi) g
      | _ -> cannot_apply "while" "wrong arguments"
  else cannot_apply "while" "the conclusion is not a hoare or a equiv"

let process_call side info (_, n as g) = 
  let process_spec side g =
    let hyps,concl = get_goal g in
    match concl.f_node, side with
    | FhoareS hs, None ->
      let (_,f,_),_ = s_last_call "call" hs.hs_s in
      let penv, qenv = LDecl.hoareF f hyps in
      penv,qenv, fun pre post -> f_hoareF pre f post
    | FbdHoareS bhs, None ->
      let (_,f,_),_ = s_last_call "call" bhs.bhs_s in
      let penv, qenv = LDecl.hoareF f hyps in
      penv,qenv, fun pre post -> 
        bdHoare_call_spec pre post f bhs.bhs_cmp bhs.bhs_bd None
    | FbdHoareS _, Some _ | FhoareS _, Some _ ->
      cannot_apply "call" "side can only be given for prhl judgements"
    | FequivS es, None ->
      let (_,fl,_),(_,fr,_),_,_ = s_last_calls "call" es.es_sl es.es_sr in
      let penv, qenv = LDecl.equivF fl fr hyps in
      penv,qenv,fun pre post -> f_equivF pre fl fr post
    | FequivS es, Some side ->
      let fstmt = match side with true -> es.es_sl | false -> es.es_sr in
      let (_,f,_),_ = s_last_call "call" fstmt in
      let penv, qenv = LDecl.hoareF f hyps in
      penv,qenv, fun pre post ->
        f_bdHoareF pre f post FHeq f_r1
    | _ -> cannot_apply "call" "the conclusion is not a hoare or a equiv" in

  let process_inv side g = 
    if side <> None then
      cannot_apply "call" "can not specify side for call with invariant";
    let hyps, concl = get_goal g in
    match concl.f_node with
    | FhoareS hs ->
      let (_,f,_),_ = s_last_call "call" hs.hs_s in
      let penv = LDecl.inv_memenv1 hyps in
      penv, fun inv -> f_hoareF inv f inv
    | FbdHoareS bhs ->
      let (_,f,_),_ = s_last_call "call" bhs.bhs_s in
      let penv = LDecl.inv_memenv1 hyps in
      penv, fun inv -> bdHoare_call_spec inv inv f bhs.bhs_cmp bhs.bhs_bd None
    | FequivS es ->
      let (_,fl,_),(_,fr,_),_,_ = s_last_calls "call" es.es_sl es.es_sr in
      let penv = LDecl.inv_memenv hyps in
      let env = LDecl.toenv hyps in
      penv, fun inv -> EcPhl.mk_inv_spec env inv fl fr
    | _ -> cannot_apply "call" "the conclusion is not a hoare or a equiv" in

  let process_upto side info g = 
    if side <> None then
      cannot_apply "call" "can not specify side for call with invariant";
    let env, _, concl = get_goal_e g in
    match concl.f_node with
    | FequivS es ->
      let (_,fl,_),(_,fr,_),_,_ = s_last_calls "call" es.es_sl es.es_sr in
      let bad,invP,invQ = EcPhlFun.process_fun_upto_info info g in
      let (topl,fl,oil,sigl),(topr,fr,_,sigr) = abstract_info2 env fl fr in
      let ml, mr = mleft, mright in
      let bad2 = Fsubst.f_subst_mem mhr mr bad in
      let eqglob = f_eqglob topl ml topr mr in
      let lpre = if oil.oi_in then [eqglob;invP] else [invP] in
      let eq_params = 
        f_eqparams fl sigl.fs_params ml fr sigr.fs_params mr in
      let eq_res = f_eqres fl sigl.fs_ret ml fr sigr.fs_ret mr in
      let pre = f_if_simpl bad2 invQ (f_ands (eq_params::lpre)) in
      let post = f_if_simpl bad2 invQ (f_ands [eq_res;eqglob;invP]) in
      bad,invP,invQ, f_equivF pre fl fr post 
    | _ -> cannot_apply "call" "the conclusion is not an equiv" in


  let tac_sub = ref (t_id None) in

  let process_cut g info = 
    match info with
    | CI_spec (pre,post) ->
      let penv,qenv,fmake = process_spec side g in
      let pre  = process_form penv pre tbool in
      let post = process_form qenv post tbool in
      fmake pre post
    | CI_inv inv ->
      let env, fmake = process_inv side g in
      let inv = process_form env inv tbool in
      tac_sub :=  (fun g -> t_on_firsts t_trivial 2 (EcPhlFun.t_fun inv g));
      fmake inv 
    | CI_upto info -> 
      let bad,p,q,form = process_upto side info g in
      let t_tr = t_or t_assumption t_trivial in
      tac_sub := (fun g -> t_on_firsts t_tr 3 (EcPhlFun.UpToLow.t_equivF_abs_upto bad p q g));
      form in
        
        
  let (juc,an), gs = process_mkn_apply (process_cut g) info g in
  
  let t_call g = 
    let (_,f) = get_node (juc, an) in
    let concl = get_concl g in
    match f.f_node, concl.f_node with
    | FhoareF hf, FhoareS _ -> 
      t_hoare_call hf.hf_pr hf.hf_po g
    | FbdHoareF hf, FbdHoareS _ ->
      t_bdHoare_call hf.bhf_pr hf.bhf_po None g
    | FequivF ef, FequivS _ ->
      t_equiv_call ef.ef_pr ef.ef_po g
    | FbdHoareF hf, FequivS _ ->
      let side = 
        match side with
        | Some side -> side
        | _ -> cannot_apply "call" "side can only be given for prhl judgements"
      in
      t_equiv_call1 side hf.bhf_pr hf.bhf_po g
    | _, _ -> cannot_apply "call" "" in

  t_seq_subgoal t_call [t_seq (t_use an gs) !tac_sub; t_id None] (juc,n)

let process_cond side g =
  let concl = get_concl g in
  let check_N () = 
    if side <> None then
      cannot_apply "cond" "Unexpected side in non relational goal" in
  if is_equivS concl then t_equiv_cond side g
  else begin 
    check_N ();
    if is_hoareS concl then t_hoare_cond g
    else if is_bdHoareS concl then t_bdHoare_cond g
    else cannot_apply "cond" "the conclusion is not a hoare or a equiv goal"
  end

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
  
let rec process_inline_all side fs g =
  let concl = get_concl g in
  match concl.f_node, side with
  | FequivS _, None ->
      t_seq
        (process_inline_all (Some true ) fs)
        (process_inline_all (Some false) fs) g
  | FequivS es, Some b ->
      let sp = pat_all fs (if b then es.es_sl else es.es_sr) in
        if   sp = []
        then t_id None g
        else t_seq
               (t_inline_equiv b sp)
               (process_inline_all side fs) g
  | FhoareS hs, None ->
      let sp = pat_all fs hs.hs_s in
        if   sp = []
        then t_id None g
        else t_seq
               (t_inline_hoare sp)
               (process_inline_all side fs) g
  | FbdHoareS bhs, None ->
      let sp = pat_all fs bhs.bhs_s in
      if   sp = []
      then t_id None g
      else t_seq
        (t_inline_bdHoare sp)
        (process_inline_all side fs) g

  | _, _ -> cannot_apply "inline" "Wrong parameters or phl/prhl judgement not found" 
  
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

let process_inline_occs side fs occs g =
  let cond = 
    if EcPath.Sx.is_empty fs then fun _ -> true
    else fun f -> EcPath.Sx.mem f fs in
  let occs = Sint.of_list occs in
  let concl = get_concl g in
  match concl.f_node, side with
  | FequivS es, Some b ->
    let sp =  pat_of_occs cond occs (if b then es.es_sl else es.es_sr) in
    t_inline_equiv b sp g 
  | FhoareS hs, None ->
    let sp =  pat_of_occs cond occs hs.hs_s in
    t_inline_hoare sp g 
  | _, _ -> assert false (* FIXME error message *)
  

let process_inline infos g =
  match infos with
  | `ByName (side, (fs, occs)) -> begin
      let hyps = get_hyps g in
      let env = LDecl.toenv hyps in
      let fs = 
        List.fold_left (fun fs f ->
          let f = EcTyping.trans_gamepath env f in
          EcPath.Sx.add f fs) EcPath.Sx.empty fs 
      in
      match occs with
      | None -> process_inline_all side fs g
      | Some occs -> process_inline_occs side fs occs g
    end

  | `ByPattern _ -> failwith "not-implemented"


(* César says: too much code repetition w.r.t. ecPhl *)
let process_bdHoare_deno info (_,n as g) = 
  let process_cut g (pre,post) = 
    let hyps,concl = get_goal g in
    let cmp, f, bd =
      match concl.f_node with
      | Fapp({f_node = Fop(op,_)}, [f;bd]) when is_pr f &&
          (EcPath.p_equal op EcCoreLib.p_eq || 
             EcPath.p_equal op EcCoreLib.p_real_le ) ->
        let cmp = if EcPath.p_equal op EcCoreLib.p_eq then FHeq else FHle in
        cmp, f, bd
      | Fapp({f_node = Fop(op,_)}, [bd;f]) when is_pr f 
          &&
          (EcPath.p_equal op EcCoreLib.p_eq || 
             EcPath.p_equal op EcCoreLib.p_real_le ) ->
        let cmp = if EcPath.p_equal op EcCoreLib.p_eq then FHeq else FHge in
        cmp, f , bd
      | _ -> cannot_apply "bdHoare_deno" 
        "the conclusion is not a suitable Pr expression" in (* FIXME error message *) 
    let _,f,_,event = destr_pr f in
    let penv, qenv = LDecl.hoareF f hyps in
    let pre  = pre  |> omap_dfl (fun p -> process_form penv p tbool) f_true in
    let post = post |> omap_dfl (fun p -> process_form qenv p tbool) event in
    f_bdHoareF pre f post cmp bd 
  in
  let (juc,an), gs = process_mkn_apply (process_cut g) info g in
  let pre,post =
    let (_,f) = get_node (juc,an) in
    let bhf = t_as_bdHoareF f in
    bhf.bhf_pr, bhf.bhf_po in
  t_on_first (t_use an gs) (t_bdHoare_deno pre post (juc,n))

let process_equiv_deno info (_,n as g) = 
  let process_cut g (pre,post) = 
    let hyps,concl = get_goal g in
    let _op, f1, f2 =
      match concl.f_node with
      | Fapp({f_node = Fop(op,_)}, [f1;f2]) when is_pr f1 && is_pr f2 -> 
        op, f1, f2
      | _ -> cannot_apply "equiv_deno" "" in (* FIXME error message *) 
    let _,fl,_,_ = destr_pr f1 in
    let _,fr,_,_ = destr_pr f2 in
    let penv, qenv = LDecl.equivF fl fr hyps in
    let pre  = pre |> omap_dfl (fun p -> process_form penv p tbool) f_true in
    (* FIXME: Benjamin : below: put a better default event instead of f_true *)
    let post = post |> omap_dfl (fun p -> process_form qenv p tbool) f_true in
    f_equivF pre fl fr post in
  let (juc,an), gs = process_mkn_apply (process_cut g) info g in
  let pre,post =
    let (_,f) = get_node (juc,an) in
    let ef = t_as_equivF f in
    ef.ef_pr, ef.ef_po in
  t_on_first (t_use an gs) (t_equiv_deno pre post (juc,n))
  
let process_ppr (phi1,phi2) g =
  let hyps,concl = get_goal g in
  let ef = t_as_equivF concl in
  let _penv,qenv = LDecl.equivF ef.ef_fl ef.ef_fr hyps in
  let phi1 = process_form_opt qenv phi1 None in
  let phi2 = process_form_opt qenv phi2 None in
  (* TODO: check for type unification *)
  let ty = f_ty phi1 in
  t_ppr ty phi1 phi2 g

let process_fel at_pos (cntr, ash, q, f_event, pred_specs,o_inv) g = 
  let hyps,concl = get_goal g in
  (* let hyps = LDecl.inv_memenv hyps in  *)
  (* code duplication from t_failure *)
  let f = match concl.f_node with
    | Fapp ({f_node=Fop(op,_)},[pr;_]) when is_pr pr 
        && EcPath.p_equal op EcCoreLib.p_real_le ->
      let (_,f,_,_) = destr_pr pr in
      f
    | _ -> 
      cannot_apply "failure event lemma" 
        "A goal of the form Pr[ _ ] <= _ was expected"
  in
  (* let env = EcEnv.Fun.prF f env in *)
  let hyps,_ = LDecl.hoareF f hyps in 
  let cntr = process_form hyps cntr tint in
  let ash = process_form hyps ash (tfun tint treal) in
  let q = process_form hyps q tint in
  let f_event = process_form hyps f_event tbool in
  let inv = match o_inv with | None -> f_true | Some inv -> process_form hyps inv tbool in
  let process_pred (f,pre) = 
    let env = LDecl.toenv hyps in
    let f = EcTyping.trans_gamepath env f in
    let penv, _ = LDecl.hoareF f hyps in
    f,process_form penv pre tbool
  in
  let pred_specs = List.map process_pred pred_specs in
  t_failure_event at_pos cntr ash q f_event pred_specs inv g

let process_hoare_bd_hoare g = t_hoare_bd_hoare g
let process_prbounded = t_prbounded
let process_prfalse = t_prfalse
let process_bdeq = t_bdeq

let process_exists_intro fs g = 
  let hyps,concl = get_goal g in
  let penv = 
    match concl.f_node with
    | FhoareF hf -> fst (LDecl.hoareF hf.hf_f hyps)
    | FhoareS hs -> LDecl.push_active hs.hs_m hyps 
    | FbdHoareF bhf ->fst (LDecl.hoareF bhf.bhf_f hyps) 
    | FbdHoareS bhs -> LDecl.push_active bhs.bhs_m hyps 
    | FequivF ef -> fst (LDecl.equivF ef.ef_fl ef.ef_fr hyps)
    | FequivS es -> LDecl.push_all [es.es_ml; es.es_mr] hyps 
    | _ -> tacuerror "cannot apply conseq rule, not a phl/prhl judgement" in  
  let fs = List.map (fun f -> process_form_opt penv f None) fs in
  t_hr_exists_intro fs g 

let process_eqobs_in (geq', ginv, eqs') g = 
  let env, hyps, concl = get_goal_e g in
  let ienv = LDecl.inv_memenv hyps in
  let es = t_as_equivS concl in
  let ml, mr =  fst es.es_ml, fst es.es_mr in
 
  let toeq ml mr f = 
    try EcPV.Mpv2.of_form env ml mr f 
    with _ -> 
      let ppe = EcPrinting.PPEnv.ofenv env in
      tacuerror "cannot recognize %a as a set of equalities" 
        (EcPrinting.pp_form ppe) f in

  let geq =
    match geq' with
    | None -> toeq mleft mright f_true
    | Some geq' ->
      let geq = process_form ienv geq' tbool in
      set_loc geq'.pl_loc (toeq mleft mright) geq in

  let ginv = ginv |> omap_dfl (fun f -> process_form ienv f tbool) f_true in
  let ifvl = EcPV.PV.fv env ml ginv in
  let ifvr = EcPV.PV.fv env mr ginv in

  let eqs = 
    match eqs' with 
    | None -> 
      begin 
        try EcPV.Mpv2.needed_eq env ml mr es.es_po 
        with _ -> tacuerror "cannot infer the set of equalities" 
      end
    | Some eqs' -> 
      let eqs = process_prhl_formula g eqs' in
      set_loc eqs'.pl_loc (toeq ml mr) eqs in

  let _, _, (log,_), _ = 
    EcPV.eqobs_in env
      (EcPhl.eqobs_inF env geq (ginv,ifvl,ifvr))
      { query = []; forproof = Mf.empty } es.es_sl es.es_sr eqs (ifvl,ifvr) in
    
  let onF _ fl fr eqo = 
    match find_eqobs_in_log log fl fr eqo with
    | Some (eqo,spec) -> (), eqo, spec 
    | None -> assert false in

  let t_eqobs eqs g =
    let concl = get_concl g in
    let es = t_as_equivS concl in
    let ml, mr = fst es.es_ml, fst es.es_mr in
    let post = EcPV.Mpv2.to_form ml mr eqs ginv in
    let pre = es.es_pr in
    t_seq_subgoal 
      (EcPhlConseq.t_equivS_conseq pre post)
      [ t_trivial;
        t_trivial;
        (fun g -> 
          t_on_last (t_try (t_seq EcPhlSkip.t_skip t_trivial))
            (t_eqobs_inS onF eqs ginv g))] 
      g in
   
  let tocut = 
    Mf.fold (fun spec eori l ->
      match eori with
      | EORI_unknown None -> spec :: l
      | _ -> l) log.forproof [] in
 
  let forproof = ref log.forproof in

  let rec t_cut_spec l g = 
    match l with
    | [] -> t_id None g
    | spec :: l ->
      let hyps = get_hyps g in
      let id = LDecl.fresh_id hyps "H" in
      forproof := Mf.add spec (EORI_unknown (Some id)) !forproof;
      t_seq_subgoal (t_cut spec)
        [ t_id None;
          t_seq (t_intros_i [id]) (t_cut_spec l)] g in
 
  let t_rec g = 
    let concl = get_concl g in
    match Mf.find_opt concl !forproof with
    | Some (EORI_adv geq) ->
      let gs =
        EcPhlFun.FunAbsLow.t_equivF_abs
          (EcPV.Mpv2.to_form mleft mright geq ginv) g in
      t_on_firsts t_trivial 2 gs 
    | Some (EORI_fun eqs) ->
      t_seq EcPhlFun.FunDefLow.t_equivF_fun_def
        (t_eqobs eqs) g 
    | Some (EORI_unknown (Some id)) ->
      t_hyp id g
    | _ -> t_fail g in
  
  t_on_last 
    (t_seq (t_eqobs eqs) (t_repeat t_rec))
    (t_cut_spec tocut g) 

(* -------------------------------------------------------------------- *)
let process_phl loc ptac g =
  let t =
    match ptac with
    | Pfun_def                  -> EcPhlFun.t_fun_def
    | Pfun_abs f                -> EcPhlFun.process_fun_abs f
    | Pfun_upto info            -> EcPhlFun.process_fun_upto info 
    | Pfun_to_code              -> EcPhlFun.t_fun_to_code 
    | Pskip                     -> EcPhlSkip.t_skip
    | Papp (dir, k, phi, f)     -> EcPhlApp.process_app dir k phi f
    | Pwp k                     -> EcPhlWp.t_wp k
    | Prcond (side, b, i)       -> EcPhlRCond.t_rcond side b i
    | Pcond side                -> process_cond side
    | Pwhile (side, (phi, vopt))-> process_while side phi vopt
    | Pfission info             -> EcPhlLoopTx.process_fission info
    | Pfusion info              -> EcPhlLoopTx.process_fusion info
    | Punroll info              -> EcPhlLoopTx.process_unroll info
    | Psplitwhile info          -> EcPhlLoopTx.process_splitwhile info
    | Pcall (side, info)        -> process_call side info
    | Pswap info                -> EcPhlSwap.process_swap info
    | Pinline info              -> process_inline info
    | Pcfold info               -> EcPhlCodeTx.process_cfold info
    | Pkill info                -> EcPhlCodeTx.process_kill info
    | Palias info               -> EcPhlCodeTx.process_alias info
    | Prnd (side, info)         -> EcPhlRnd.process_rnd side info
    | Pconseq (nm,info)         -> EcPhlConseq.process_conseq nm info
    | Phr_exists_elim           -> t_hr_exists_elim
    | Phr_exists_intro fs       -> process_exists_intro fs
    | Pexfalso                  -> EcPhlExfalso.t_exfalso
    | Pbdhoaredeno info         -> process_bdHoare_deno info
    | PPr (phi1,phi2)           -> process_ppr (phi1,phi2)
    | Pfel (at_pos,info)        -> process_fel at_pos info
    | Pequivdeno info           -> process_equiv_deno info
    | Phoare | Pbdhoare         -> process_hoare_bd_hoare
    | Pprbounded                -> process_prbounded
    | Pprfalse                  -> process_prfalse
    | Ppr_rewrite s             -> t_pr_rewrite s 
    | Pbdeq                     -> process_bdeq
    | Peqobs_in info            -> process_eqobs_in info
    | Ptrans_stmt info          -> EcPhlTrans.process_equiv_trans info
    | Psp      arg              -> t_sp arg
  in
    set_loc loc t g
