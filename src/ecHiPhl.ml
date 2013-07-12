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
open EcPhl

module TT = EcTyping
module UE = EcUnify.UniEnv

(* -------------------------------------------------------------------- *)
let process_phl_form ty g phi =
  let hyps, concl = get_goal g in
  let m = 
    try 
      let hs = set_loc phi.pl_loc destr_hoareS concl in
      hs.hs_m
    with _ ->
      let hs = set_loc phi.pl_loc destr_bdHoareS concl in
      hs.bhs_m
  in
  let hyps = LDecl.push_active m hyps in
  process_form hyps phi ty

let process_prhl_form ty g phi =
  let hyps, concl = get_goal g in
  let es = set_loc phi.pl_loc destr_equivS concl in
  let hyps = LDecl.push_all [es.es_ml; es.es_mr] hyps in
  process_form hyps phi ty

let process_phl_formula = process_phl_form tbool

let process_prhl_formula = process_prhl_form tbool

let process_phl_bd_info dir g bd_info = 
  match bd_info with
  | PAppNone -> 
    let hs = destr_bdHoareS (get_concl g) in
    let f1, f2 = 
       match dir with
      | Backs  -> hs.bhs_bd, f_r1 
      | Fwds   -> f_r1, hs.bhs_bd in
    f_true, f1, f2, f_r0, f_r1 (* The last argument will not be used *)
  | PAppSingle f -> 
    let f = process_phl_formula g f in
    let hs = destr_bdHoareS (get_concl g) in
    let f1, f2 = 
      match dir with
      | Backs  -> f_real_div hs.bhs_bd f, f 
      | Fwds   -> f, f_real_div hs.bhs_bd f in
    f_true, f1, f2, f_r0, f_r1
    
  | PAppMult(phi,f1,f2,g1,g2) ->
    let phi = omap_dfl phi f_true (process_phl_formula g) in
    let check_0 f = 
      if not (f_equal f f_r0) then tacuerror "the formula should be 0%%r" in
    let process_f (f1,f2) = 
      match f1, f2 with
      | None, None -> assert false (* Not accepted by the parser *)
      | Some f, None -> 
        let loc = f.pl_loc in
        let f = process_phl_form treal g f in
        set_loc loc check_0 f;
        f, f_r1
      | None, Some f ->
        let loc = f.pl_loc in
        let f = process_phl_form treal g f in
        set_loc loc check_0 f;
        f_r1, f
      | Some f1, Some f2 ->
        process_phl_form treal g f1, process_phl_form treal g f2 in
    let f1, f2 = process_f (f1,f2) in
    let g1, g2 = process_f (g1,g2) in
    (phi,f1,f2,g1,g2)

let process_app dir k phi bd_info g =
  let concl = get_concl g in
  match k, bd_info with
  | Single i, PAppNone when is_hoareS concl ->
    let phi = process_phl_formula g phi in
    t_hoare_app i phi g
  | Single i, _ when is_bdHoareS concl ->
    let pR = process_phl_formula g phi in
    let (phi,f1,f2,f3,f4) = process_phl_bd_info dir g bd_info in
    t_bdHoare_app i (phi,pR,f1,f2,f3,f4) g
  | Double(i,j), PAppNone ->
    let phi = process_prhl_formula g phi in
    t_equiv_app (i,j) phi g
  | Single _, PAppNone ->
    cannot_apply "app" "wrong position parameter"
  | _, _ ->
      cannot_apply "app" "optional bound parameter not supported"

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

let process_fission (side, cpos, infos) g =
  t_fission side cpos infos g

let process_fusion (side, cpos, infos) g =
  t_fusion side cpos infos g

let process_unroll (side, cpos) g =
  t_unroll side cpos g

let process_exp hyps e oty =
  let env = LDecl.toenv hyps in
  let ue  = EcUnify.UniEnv.create (Some (LDecl.tohyps hyps).h_tvar) in
  let e   = TT.transexpcast env ue oty e in
    EcTypes.e_uni (EcUnify.UniEnv.close ue) e

let process_phl_exp side e ty g =
  let (hyps, concl) = get_goal g in

  let (m, _) =
    try  destr_programS side concl
    with _ -> tacuerror "conclusion not of the right form"
  in

  let hyps = LDecl.push_active m hyps in
  process_exp hyps e ty

let process_splitwhile (b, side, cpos) g =
  let b = process_phl_exp side b tbool g in
    t_splitwhile b side cpos g

let process_fun_upto_info (bad, p, o) g =
  let hyps = get_hyps g in
  let env' = LDecl.inv_memenv hyps in 
  let p = process_form env' p tbool in
  let q = 
    match o with
    | None -> EcFol.f_true
    | Some q -> process_form env' q tbool in
  let bad = 
    let env' = LDecl.push_active (EcFol.mhr,None) hyps in
    process_form env' bad tbool in
  bad, p, q

let process_fun_upto info g =
  let (bad,p,q) = process_fun_upto_info info g in
  t_equivF_abs_upto bad p q g

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
      let bad,invP,invQ = process_fun_upto_info info g in
      let topl,fl,oil,sigl,topr,fr,_,sigr = abstract_info2 env fl fr in
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
    
  let t_fun inv g = 
    let env, _, concl = get_goal_e g in
    match concl.f_node with
    | FhoareF h ->
      if NormMp.is_abstract_fun h.hf_f env then t_hoareF_abs inv g
      else t_hoareF_fun_def g
    | FbdHoareF h ->
       if NormMp.is_abstract_fun h.bhf_f env then t_bdHoareF_abs inv g
      else t_bdHoareF_fun_def g
    | FequivF e ->
       if NormMp.is_abstract_fun e.ef_fl env then t_equivF_abs inv g
      else t_equivF_fun_def g
    | _ -> assert false in


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
      tac_sub :=  (fun g -> t_on_firsts t_trivial 2 (t_fun inv g));
      fmake inv 
    | CI_upto info -> 
      let bad,p,q,form = process_upto side info g in
      let t_tr = t_or t_assumption t_trivial in
      tac_sub := (fun g -> t_on_firsts t_tr 3 (t_equivF_abs_upto bad p q g));
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


let stmt_length side concl = 
  match concl.f_node, side with
  | FhoareS hs, None -> List.length hs.hs_s.s_node
  | FbdHoareS bhs, None -> List.length bhs.bhs_s.s_node
  | FequivS es, Some side -> 
    List.length (if side then es.es_sl.s_node else es.es_sr.s_node)
  | FequivS _, None -> assert false 
  | _ -> cannot_apply "stmt_length" "a phl/pbhl/prhl judgement was expected"

let rec process_swap1 info g =
  let side,pos = info.pl_desc in
  let concl = get_concl g in
  if is_equivS concl && side = None then
    t_seq (process_swap1 {info with pl_desc = (Some true, pos)})
      (process_swap1 {info with pl_desc = (Some false, pos)}) g 
  else
    let p1, p2, p3 = match pos with
      | SKbase(p1,p2,p3) -> p1, p2, p3
      | SKmove p ->
        if 0 < p then 1, 2, p+1
        else if p < 0 then
          let len = stmt_length side concl in
          len+p, len, len
        else (* p = 0 *) 0,0,0
      | SKmovei(i,p) ->
        if 0 < p then i, i+1, i+p
        else if p < 0 then i+p, i, i
        else (* p = 0 *) 0,0,0
      | SKmoveinter(i1,i2,p) ->
        if 0 < p then i1, i2+1, i2+p
        else if p < 0 then i1+p, i1, i2
        else (* p = 0 *) 0,0,0
    in
    let tac =
      if p1 = 0 then t_id None else
        match side with
        | None when is_hoareS concl ->
          t_hoare_swap p1 p2 p3
        | None when is_bdHoareS concl ->
          t_bdHoare_swap p1 p2 p3
        | None ->
          t_seq (process_swap1 {info with pl_desc = (Some true, pos)})
            (process_swap1 {info with pl_desc = (Some false, pos)})
        | Some side ->
          t_equiv_swap side p1 p2 p3
    in
    set_loc info.pl_loc tac g


let process_swap info =
  t_lseq (List.map process_swap1 info)

let process_cfold (side, cpos, olen) g =
  t_cfold side cpos olen g

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

let process_kill (side, cpos, len) g =
  t_kill side cpos len g

let process_alias (side, cpos, id) g =
  t_alias side cpos id g

let process_rnd side tac_info g =
  let _, _, concl = get_goal_e g in
  match side, tac_info with 
    | None, PNoRndParams when is_hoareS concl -> t_hoare_rnd g
    | None, _ when is_bdHoareS concl ->
      let tac_info = match tac_info with 
        | PNoRndParams -> PNoRndParams
        | PSingleRndParam p ->
          PSingleRndParam (fun t -> process_phl_form (tfun t tbool) g p)
        | PMultRndParams ((phi,d1,d2,d3,d4),p) -> 
          let p t = omap p (process_phl_form (tfun t tbool) g) in
          let phi = process_phl_form tbool g phi in
          let d1 = process_phl_form treal g d1 in
          let d2 = process_phl_form treal g d2 in
          let d3 = process_phl_form treal g d3 in
          let d4 = process_phl_form treal g d4 in
          PMultRndParams ((phi,d1,d2,d3,d4),p)
        | _ -> tacuerror "Wrong tactic arguments"
      in
      t_bd_hoare_rnd tac_info g
    | _ when is_equivS concl ->
      let process_form f ty1 ty2 = process_prhl_form (tfun ty1 ty2) g f in
      let bij_info = match tac_info with
        | PNoRndParams -> None, None
        | PSingleRndParam f -> Some (process_form f), None
        | PTwoRndParams (f, finv) -> Some (process_form f), Some (process_form finv)
        | _ -> tacuerror "Wrong tactic arguments"
      in
      t_equiv_rnd side bij_info g
    | _ -> cannot_apply "rnd" "unexpected instruction or wrong arguments"

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
    let pre  = omap_dfl pre  f_true (fun p -> process_form penv p tbool) in
    let post = omap_dfl post event  (fun p -> process_form qenv p tbool) in
    f_bdHoareF pre f post cmp bd 
  in
  let (juc,an), gs = process_mkn_apply (process_cut g) info g in
  let pre,post =
    let (_,f) = get_node (juc,an) in
    let bhf = destr_bdHoareF f in
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
    let pre  = omap_dfl pre  f_true (fun p -> process_form penv p tbool) in
    (* FIXME: Benjamin : below: put a better default event instead of f_true *)
    let post = omap_dfl post f_true (fun p -> process_form qenv p tbool) in
    f_equivF pre fl fr post in
  let (juc,an), gs = process_mkn_apply (process_cut g) info g in
  let pre,post =
    let (_,f) = get_node (juc,an) in
    let ef = destr_equivF f in
    ef.ef_pr, ef.ef_po in
  t_on_first (t_use an gs) (t_equiv_deno pre post (juc,n))

let process_conseq notmod info (_, n as g) =
  let process_cut g ((pre,post),bd) =
    let hyps,concl = get_goal g in        
    let ensure_none o =
      if o <> None then tacuerror "Can not give a bound here." in
    let penv, qenv, gpre, gpost, fmake = 
      match concl.f_node with
      | FhoareF hf ->
        let penv, qenv = LDecl.hoareF hf.hf_f hyps in
        penv, qenv, hf.hf_pr, hf.hf_po, 
        (fun pre post bd -> ensure_none bd;f_hoareF pre hf.hf_f post)
      | FhoareS hs ->
        let env = LDecl.push_active hs.hs_m hyps in
        env, env, hs.hs_pr, hs.hs_po,
        (fun pre post bd -> ensure_none bd;f_hoareS_r { hs with hs_pr = pre; hs_po = post })
      | FbdHoareF bhf ->
        let penv, qenv = LDecl.hoareF bhf.bhf_f hyps in
        penv, qenv, bhf.bhf_pr, bhf.bhf_po, 
        (fun pre post bd -> 
          let cmp,bd = odfl (None,bhf.bhf_bd) bd in
          let cmp = odfl bhf.bhf_cmp cmp in
          f_bdHoareF pre bhf.bhf_f post cmp bd)
      | FbdHoareS bhs ->
        let env = LDecl.push_active bhs.bhs_m hyps in
        env, env, bhs.bhs_pr, bhs.bhs_po,
        (fun pre post bd -> 
          let cmp,bd = odfl (None,bhs.bhs_bd) bd in
          let cmp = odfl bhs.bhs_cmp cmp in
          f_bdHoareS_r 
            { bhs with bhs_pr = pre; bhs_po = post; bhs_cmp = cmp; bhs_bd = bd})
      | FequivF ef ->
        let penv, qenv = LDecl.equivF ef.ef_fl ef.ef_fr hyps in
        penv, qenv, ef.ef_pr, ef.ef_po,
        (fun pre post bd -> ensure_none bd;f_equivF pre ef.ef_fl ef.ef_fr post)
      | FequivS es -> 
        let env = LDecl.push_all [es.es_ml; es.es_mr] hyps in
        env, env, es.es_pr, es.es_po,
        (fun pre post bd -> ensure_none bd;f_equivS_r { es with es_pr = pre; es_po = post }) 
      | _ -> tacuerror "cannot apply conseq rule, not a phl/prhl judgement"
    in
    let pre = match pre with
      | None -> gpre 
      | Some pre -> process_form penv pre tbool in
    let post = match post with
      | None -> gpost 
      | Some post -> process_form qenv post tbool in
    let bd = match bd with
      | None -> None
      | Some (cmp,bd) -> 
        let bd = process_form penv bd treal in
        let cmp  = omap cmp (function PFHle -> FHle | PFHeq -> FHeq | PFHge -> FHge) in
        Some (cmp,bd) in
    fmake pre post bd
  in
  let (juc,an), gs = process_mkn_apply (process_cut g) info g in
  let lt = ref [t_use an gs] in
  let t_trivial = t_try (t_lseq [t_simplify_nodelta;t_split;t_fail]) in
  let t_conseq = 
    let (_,f) = get_node (juc,an) in
    match f.f_node with
    | FhoareF hf   -> 
      if notmod then t_hoareF_conseq_nm hf.hf_pr hf.hf_po
      else t_hoareF_conseq hf.hf_pr hf.hf_po
    | FhoareS hs   -> 
      if notmod then t_hoareS_conseq_nm hs.hs_pr hs.hs_po
      else t_hoareS_conseq hs.hs_pr hs.hs_po 
    | FbdHoareF hf ->
      let t1 = 
        if notmod then t_bdHoareF_conseq_nm hf.bhf_pr hf.bhf_po
        else t_bdHoareF_conseq hf.bhf_pr hf.bhf_po in
      let t2 = t_bdHoareF_conseq_bd hf.bhf_cmp hf.bhf_bd in
      lt := t_trivial :: !lt;
      t_seq_subgoal t1 [t_id None; t_id None; t2]
    | FbdHoareS hs -> 
      let t1 = 
        if notmod then t_bdHoareS_conseq_nm hs.bhs_pr hs.bhs_po
        else t_bdHoareS_conseq hs.bhs_pr hs.bhs_po in
      let t2 = t_bdHoareS_conseq_bd hs.bhs_cmp hs.bhs_bd in
      lt := t_trivial :: !lt;
      t_seq_subgoal t1 [t_id None; t_id None; t2]
    | FequivF ef   -> 
      if notmod then t_equivF_conseq_nm ef.ef_pr ef.ef_po
      else t_equivF_conseq ef.ef_pr ef.ef_po
    | FequivS es   -> 
      if notmod then t_equivS_conseq_nm es.es_pr es.es_po 
      else t_equivS_conseq es.es_pr es.es_po 
    | _ -> tacuerror "cannot apply conseq rule, not a phl/prhl judgement" in
  t_subgoal (t_trivial :: t_trivial :: !lt) 
    (t_conseq (juc,n)) 
  
let process_fun_abs inv g =
  let hyps,concl = get_goal g in
  if is_equivF concl then
    let env' = LDecl.inv_memenv hyps in
    let inv = process_form env' inv tbool in
    t_equivF_abs inv g
  else
    let env' = LDecl.inv_memenv1 hyps in
    let inv = process_form env' inv tbool in
    if is_bdHoareF concl then t_bdHoareF_abs inv g
    else if is_hoareF concl then t_hoareF_abs inv g
    else cannot_apply "fun" "equiv or probabilistic hoare triple was expected"

let process_exfalso g =
  let concl = get_concl g in
  t_or (t_hr_exfalso)
    (t_seq_subgoal (t_hr_conseq f_false (get_post concl))
        [t_id None; t_trivial; t_hr_exfalso ]) g

let process_ppr (phi1,phi2) g =
  let hyps,concl = get_goal g in
  let ef = destr_equivF concl in
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
  let es = destr_equivS concl in
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

  let ginv = omap_dfl ginv f_true (fun f -> process_form ienv f tbool) in
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
    let es = destr_equivS concl in
    let ml, mr = fst es.es_ml, fst es.es_mr in
    let post = EcPV.Mpv2.to_form ml mr eqs ginv in
    let pre = es.es_pr in
    t_seq_subgoal 
      (t_equivS_conseq pre post)
      [ t_trivial;
        t_trivial;
        (fun g -> 
          t_on_last (t_try (t_seq EcPhl.t_skip t_trivial))
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
      let gs = t_equivF_abs (EcPV.Mpv2.to_form mleft mright geq ginv) g in
      t_on_firsts t_trivial 2 gs 
    | Some (EORI_fun eqs) ->
      t_seq t_equivF_fun_def
        (t_eqobs eqs) g 
    | Some (EORI_unknown (Some id)) ->
      t_hyp id g
    | _ -> t_fail g in
  
  t_on_last 
    (t_seq (t_eqobs eqs)
       (t_repeat t_rec))
    (t_cut_spec tocut g) 
  

(* -------------------------------------------------------------------- *)
let process_phl loc ptac g =
  let t =
    match ptac with
    | Pfun_def                  -> EcPhl.t_fun_def
    | Pfun_abs f                -> process_fun_abs f
    | Pfun_upto info            -> process_fun_upto info 
    | Pfun_to_code              -> EcPhl.t_fun_to_code 
    | Pskip                     -> EcPhl.t_skip
    | Papp (dir, k, phi, f)     -> process_app dir k phi f
    | Pwp k                     -> t_wp k
    | Prcond (side, b, i)       -> t_rcond side b i
    | Pcond side                -> process_cond side
    | Pwhile (side, (phi, vopt))  -> process_while side phi vopt
    | Pfission info             -> process_fission info
    | Pfusion info              -> process_fusion info
    | Punroll info              -> process_unroll info
    | Psplitwhile info          -> process_splitwhile info
    | Pcall (side, info)        -> process_call side info
    | Pswap info                -> process_swap info
    | Pcfold info               -> process_cfold info
    | Pinline info              -> process_inline info
    | Pkill info                -> process_kill info
    | Palias info               -> process_alias info
    | Prnd (side, info)         -> process_rnd side info
    | Pconseq (nm,info)         -> process_conseq nm info
    | Phr_exists_elim           -> t_hr_exists_elim
    | Phr_exists_intro fs       -> process_exists_intro fs
    | Pexfalso                  -> process_exfalso
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
  in
    set_loc loc t g
