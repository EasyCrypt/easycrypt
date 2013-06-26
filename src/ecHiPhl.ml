(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcParsetree
open EcLocation
open EcTypes
open EcModules
open EcFol
open EcEnv
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

let process_phl_bd_info g bd_info = match bd_info with
  | PAppNone -> AppNone
  | PAppSingle f -> AppSingle (process_phl_form treal g f)
  | PAppMult(f1,f2,f3,f4) ->
    let f1 = process_phl_form treal g f1 in
    let f2 = process_phl_form treal g f2 in
    let f3 = process_phl_form treal g f3 in
    let f4 = process_phl_form treal g f4 in
    AppMult(f1,f2,f3,f4)

let process_app dir k phi bd_info g =
  let concl = get_concl g in
  match k, bd_info with
    | Single i, PAppNone when is_hoareS concl ->
      let phi = process_phl_formula g phi in
      t_hoare_app i phi g
    | Single i, _ when is_bdHoareS concl ->
      let phi = process_phl_formula g phi in
      let bd_info = process_phl_bd_info g bd_info in
      t_bdHoare_app dir i phi bd_info g
    | Double(i,j), PAppNone ->
      let phi = process_prhl_formula g phi in
      t_equiv_app (i,j) phi g
    | Single _, PAppNone ->
      cannot_apply "app" "wrong position parameter"
    | _, _ ->
      cannot_apply "app" "optional bound parameter not supported"

let process_while phi vrnt_opt info g =
  let concl = get_concl g in
  if is_hoareS concl then
    match vrnt_opt,info with
      | None, None ->
        t_hoare_while (process_phl_formula g phi) g
      | _ -> cannot_apply "while" "wrong arguments"
  else if is_bdHoareS concl then
    match vrnt_opt,info with
      | Some vrnt, info ->
        t_bdHoare_while 
          (process_phl_formula g phi) 
          (process_phl_form tint g vrnt) 
          (omap info (fun (bd,i) -> process_phl_form treal g bd,
            process_phl_form tint g i))
          g
      | _ -> cannot_apply "while" "wrong arguments"
  else if is_equivS concl then
    match vrnt_opt,info with
      | None, None ->
        t_equiv_while (process_prhl_formula g phi) g
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

let process_call side pre post g =
  let hyps,concl = get_goal g in
  match concl.f_node, side with
  | FhoareS hs, None ->
    let (_,f,_),_ = s_last_call "call" hs.hs_s in
    let penv, qenv = LDecl.hoareF f hyps in
    let pre  = process_form penv pre tbool in
    let post = process_form qenv post tbool in
    t_hoare_call pre post g
  | FbdHoareS bhs, None ->
    let (_,f,_),_ = s_last_call "call" bhs.bhs_s in
    let penv, qenv = LDecl.hoareF f hyps in
    let pre  = process_form penv pre tbool in
    let post = process_form qenv post tbool in
    t_bdHoare_call pre post None g
  | FbdHoareS _, Some _ | FhoareS _, Some _ ->
    cannot_apply "call" "side can only be given for prhl judgements"
  | FequivS es, None ->
    let (_,fl,_),(_,fr,_),_,_ = s_last_calls "call" es.es_sl es.es_sr in
    let penv, qenv = LDecl.equivF fl fr hyps in
    let pre  = process_form penv pre tbool in
    let post = process_form qenv post tbool in
    t_equiv_call pre post g
  | FequivS es, Some side ->
    let fstmt = match side with true -> es.es_sl | false -> es.es_sr in
    let (_,f,_),_ = s_last_call "call" fstmt in
    let penv, qenv = LDecl.hoareF f hyps in
    let pre  = process_form penv pre tbool in
    let post = process_form qenv post tbool in
    t_equiv_call1 side pre post g
  | _ -> cannot_apply "call" "the conclusion is not a hoare or a equiv"

let process_cond side g =
  let concl = get_concl g in
  if is_equivS concl then t_equiv_cond side g
  else if is_hoareS concl || is_bdHoareS concl then
    match side with
      | Some _ -> cannot_apply "cond" "Unexpected side in non relational goal"
      | None ->
        if is_hoareS concl then t_hoare_cond g else t_bdHoare_cond g
  else cannot_apply "cond" "the conclusion is not a hoare or a equiv goal"

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
  let concl = get_concl g in
  match side, tac_info with 
    | None, (None, None) when is_hoareS concl -> t_hoare_rnd g
    | None, (opt_bd, opt_event) when is_bdHoareS concl ->
      let opt_bd = omap opt_bd (process_phl_form treal g)  in
      let event ty = omap opt_event (process_phl_form (tfun ty tbool) g) in
      t_bd_hoare_rnd (opt_bd,event) g
    | _ when is_equivS concl ->
      let process_form f ty1 ty2 = process_prhl_form (tfun ty1 ty2) g f in
      let bij_info = match tac_info with
        | None,None -> None, None
        | Some f, None | None, Some f -> Some (process_form f), None
        | Some f, Some finv -> Some (process_form f), Some (process_form finv)
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

let process_conseq info (_, n as g) =
  let t_pre = ref (t_id None) and t_post = ref (t_id None) in
  let process_cut g (pre,post) =
    let hyps,concl = get_goal g in        
    let penv, qenv, gpre, gpost, fmake = 
      match concl.f_node with
      | FhoareF hf ->
        let penv, qenv = LDecl.hoareF hf.hf_f hyps in
        penv, qenv, hf.hf_pr, hf.hf_po, 
        (fun pre post -> f_hoareF pre hf.hf_f post)
      | FhoareS hs ->
        let env = LDecl.push_active hs.hs_m hyps in
        env, env, hs.hs_pr, hs.hs_po,
        (fun pre post -> f_hoareS_r { hs with hs_pr = pre; hs_po = post })
      | FbdHoareF bhf ->
        let penv, qenv = LDecl.hoareF bhf.bhf_f hyps in
        penv, qenv, bhf.bhf_pr, bhf.bhf_po, 
        (fun pre post -> f_bdHoareF pre bhf.bhf_f post bhf.bhf_cmp bhf.bhf_bd)
      | FbdHoareS bhs ->
        let env = LDecl.push_active bhs.bhs_m hyps in
        env, env, bhs.bhs_pr, bhs.bhs_po,
        (fun pre post -> f_bdHoareS_r { bhs with bhs_pr = pre; bhs_po = post })
      | FequivF ef ->
        let penv, qenv = LDecl.equivF ef.ef_fl ef.ef_fr hyps in
        penv, qenv, ef.ef_pr, ef.ef_po,
        (fun pre post -> f_equivF pre ef.ef_fl ef.ef_fr post)
      | FequivS es -> 
        let env = LDecl.push_all [es.es_ml; es.es_mr] hyps in
        env, env, es.es_pr, es.es_po,
        (fun pre post -> f_equivS_r { es with es_pr = pre; es_po = post }) 
      | _ -> tacuerror "cannot apply conseq rule, not a phl/prhl judgement"
    in
    let pre = match pre with
      | None -> t_pre := t_progress (t_id None); gpre 
      | Some pre -> process_form penv pre tbool in
    let post = match post with
      | None -> t_post := t_progress (t_id None); gpost 
      | Some post -> process_form qenv post tbool in
    fmake pre post in
  let (juc,an), gs = process_mkn_apply (process_cut g) info g in
  let t_conseq = 
    let (_,f) = get_node (juc,an) in
    match f.f_node with
    | FhoareF hf   -> t_hoareF_conseq hf.hf_pr hf.hf_po
    | FhoareS hs   -> t_hoareS_conseq hs.hs_pr hs.hs_po
    | FbdHoareF hf -> t_bdHoareF_conseq hf.bhf_pr hf.bhf_po
    | FbdHoareS hs -> t_bdHoareS_conseq hs.bhs_pr hs.bhs_po
    | FequivF ef   -> t_equivF_conseq ef.ef_pr ef.ef_po
    | FequivS es   -> t_equivS_conseq es.es_pr es.es_po 
    | _ -> assert false (* FIXME error message *) in
  t_seq_subgoal t_conseq
    [!t_pre; !t_post; t_use an gs] (juc,n)
  
let process_fun_abs inv g =
  let hyps,concl = get_goal g in
  let env' = LDecl.inv_memenv hyps in
  let inv = process_form env' inv tbool in
  if is_equivF concl then t_equivF_abs inv g
  else if is_bdHoareF concl then t_bdHoareF_abs inv g
  else if is_hoareF concl then t_hoareF_abs inv g
  else cannot_apply "fun" "equiv or probabilistic hoare triple was expected"

let process_exfalso g =
  let concl = get_concl g in
  let t_trivial = t_progress (t_id None) in
  if is_hoareF concl then   
    let hf = destr_hoareF concl in
    t_or 
      (t_hoareF_exfalso)
      (t_seq_subgoal 
         (t_hoareF_conseq f_false hf.hf_po) 
         [t_id None; t_trivial; t_hoareF_exfalso]) g
  else if is_hoareS concl then
    let hs = destr_hoareS concl in
    t_or 
      (t_hoareS_exfalso)
      (t_seq_subgoal 
         (t_hoareS_conseq f_false hs.hs_po) 
         [t_id None; t_trivial; t_hoareS_exfalso]) g
  else if is_bdHoareF concl then
    let bhf = destr_bdHoareF concl in
    t_or 
      (t_bdHoareF_exfalso)
      (t_seq_subgoal 
         (t_bdHoareF_conseq f_false bhf.bhf_po) 
         [t_id None; t_trivial; t_bdHoareF_exfalso]) g
  else if is_bdHoareS concl then
    let bhs = destr_bdHoareS concl in
    t_or 
      (t_bdHoareS_exfalso)
      (t_seq_subgoal 
         (t_bdHoareS_conseq f_false bhs.bhs_po) 
         [t_id None; t_trivial; t_bdHoareS_exfalso]) g
  else if is_equivF concl then
    let ef = destr_equivF concl in
    t_or 
      (t_equivF_exfalso)
      (t_seq_subgoal 
         (t_equivF_conseq f_false ef.ef_po) 
         [t_id None; t_trivial; t_equivF_exfalso]) g
  else if is_equivS concl then
    let es = destr_equivS concl in
    t_or 
      (t_equivS_exfalso)
      (t_seq_subgoal 
         (t_equivS_conseq f_false es.es_po) 
         [t_id None; t_trivial; t_equivS_exfalso]) g
  else assert false
 
let process_fun_upto (bad, p, o) g =
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
  t_equivF_abs_upto bad p q g

let process_ppr (phi1,phi2) g =
  let hyps,concl = get_goal g in
  let ef = destr_equivF concl in

  let _penv,qenv = LDecl.equivF ef.ef_fl ef.ef_fr hyps in

  let phi1 = process_form qenv phi1 tbool in
  let phi2 = process_form qenv phi2 tbool in
  t_ppr phi1 phi2 g

let process_fel at_pos (cntr, delta, q, f_event, some_p) g = 
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
  let delta = process_form hyps delta treal in
  let q = process_form hyps q tint in
  let f_event = process_form hyps f_event tbool in
  let some_p = process_form hyps some_p tbool in
  t_failure_event at_pos cntr delta q f_event some_p g

let process_hoare_bd_hoare g = t_hoare_bd_hoare g
let process_prbounded = t_prbounded
let process_prfalse = t_prfalse
let process_pror = t_pror
let process_bdeq = t_bdeq




let process_eqobs_in (glob,loc,inv) g = 
  let glob = process_prhl_formula g glob in
  let loc = process_prhl_formula g loc in
  let inv = process_prhl_formula g inv in
  let env, _, concl = get_goal_e g in
  let es = destr_equivS concl in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  (* TODO check glob for glob and inv *)
  let eqglob = EcPV.Mpv2.of_form env ml mr glob in
  let eqloc  = EcPV.Mpv2.of_form env ml mr loc in
  let eqs = EcPV.Mpv2.union eqglob eqloc in
  let post = EcPV.Mpv2.to_form ml mr eqs inv in
  let pre = es.es_pr in
  let t_pre = 
    let h = EcIdent.create "_" in
    t_seq (t_intros_i [EcIdent.create "_";EcIdent.create "_"; h])
      (t_hyp h) in
  t_seq_subgoal (t_equivS_conseq pre post)
    [ t_pre;
      t_trivial;
      t_eqobs_inS (fun _ _ _ _ -> raise Not_found) eqs inv ]

     g
(*
  
*)  

  
  

(* -------------------------------------------------------------------- *)
let process_phl loc ptac g =
  let t =
    match ptac with
    | Pfun_def                  -> EcPhl.t_fun_def
    | Pfun_abs f                -> process_fun_abs f
    | Pfun_upto info            -> process_fun_upto info 
    | Pskip                     -> EcPhl.t_skip
    | Papp (dir, k, phi, f)     -> process_app dir k phi f
    | Pwp k                     -> t_wp k
    | Prcond (side, b, i)       -> t_rcond side b i
    | Pcond side                -> process_cond side
    | Pwhile (phi, vopt, info)  -> process_while phi vopt info
    | Pfission info             -> process_fission info
    | Pfusion info              -> process_fusion info
    | Punroll info              -> process_unroll info
    | Psplitwhile info          -> process_splitwhile info
    | Pcall (side, (pre, post)) -> process_call side pre post
    | Pswap info                -> process_swap info
    | Pcfold info               -> process_cfold info
    | Pinline info              -> process_inline info
    | Pkill info                -> process_kill info
    | Palias info               -> process_alias info
    | Prnd (side, info)         -> process_rnd side info
    | Pconseq info              -> process_conseq info
    | Pexfalso                  -> process_exfalso
    | Pbdhoaredeno info         -> process_bdHoare_deno info
    | PPr (phi1,phi2)           -> process_ppr (phi1,phi2)
    | Pfel (at_pos,info)        -> process_fel at_pos info
    | Pequivdeno info           -> process_equiv_deno info
    | Phoare | Pbdhoare         -> process_hoare_bd_hoare
    | Pprbounded                -> process_prbounded
    | Pprfalse                  -> process_prfalse
    | Ppror                     -> process_pror
    | Pbdeq                     -> process_bdeq
    | Peqobs_in info            -> process_eqobs_in info
  in
    set_loc loc t g
