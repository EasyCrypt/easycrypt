(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcParsetree
open EcLocation
open EcTypes
open EcModules
open EcFol

open EcBaseLogic
open EcLogic
open EcHiLogic
open EcPhl

module TT = EcTyping
module UE = EcUnify.UniEnv

(* -------------------------------------------------------------------- *)
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

let process_phl_bd_info env g bd_info = match bd_info with
  | PAppNone -> AppNone
  | PAppSingle f -> AppSingle (process_phl_form treal env g f)
  | PAppMult(f1,f2,f3,f4) ->
    let f1 = process_phl_form treal env g f1 in
    let f2 = process_phl_form treal env g f2 in
    let f3 = process_phl_form treal env g f3 in
    let f4 = process_phl_form treal env g f4 in
    AppMult(f1,f2,f3,f4)

let process_app env dir k phi bd_info g =
  let concl = get_concl g in
  match k, bd_info with
    | Single i, PAppNone when is_hoareS concl ->
      let phi = process_phl_formula env g phi in
      t_hoare_app i phi g
    | Single i, _ when is_bdHoareS concl ->
      let phi = process_phl_formula env g phi in
      let bd_info = process_phl_bd_info env g bd_info in
      t_bdHoare_app dir i phi bd_info g
    | Double(i,j), PAppNone ->
      let phi = process_prhl_formula env g phi in
      t_equiv_app (i,j) phi g
    | Single _, PAppNone ->
      cannot_apply "app" "wrong position parameter"
    | _, _ ->
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
  let e   = TT.transexpcast env ue oty e in
    EcTypes.e_uni (EcUnify.UniEnv.close ue) e

let process_phl_exp env side e ty g =
  let (hyps, concl) = get_goal g in

  let (m, _) =
    try  destr_programS side concl
    with _ -> tacuerror "conclusion not of the right form"
  in

  let env = EcEnv.Memory.push_active m env in
    process_exp env hyps e ty

let process_splitwhile env (b, side, cpos) g =
  let b = process_phl_exp env side b tbool g in
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
  | FbdHoareS bhs, None ->
    let (_,f,_),_ = s_last_call "call" bhs.bhs_s in
    let penv, qenv = EcEnv.Fun.hoareF f env in
    let pre  = process_form penv hyps pre tbool in
    let post = process_form qenv hyps post tbool in
    t_bdHoare_call env pre post None g
  | FbdHoareS _, Some _ | FhoareS _, Some _ ->
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

let process_kill env (side, cpos, len) g =
  t_kill env side cpos len g

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

(* César says: too much code repetition w.r.t. ecPhl *)
let process_bdHoare_deno env info (_,n as g) = 
  let process_cut env g (pre,post) = 
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
            (EcPath.p_equal op EcCoreLib.p_eq) ->
        FHeq, f , bd
      | _ -> cannot_apply "bdHoare_deno" 
        "the conclusion is not a suitable Pr expression" in (* FIXME error message *) 
    let _,f,_,event = destr_pr f in
    let penv, qenv = EcEnv.Fun.hoareF f env in
    let pre  = omap_dfl pre  f_true (fun p -> process_form penv hyps p tbool) in
    let post = omap_dfl post event  (fun p -> process_form qenv hyps p tbool) in
    f_bdHoareF pre f post cmp bd 
  in
  let (juc,an), gs = process_mkn_apply process_cut env info g in
  let pre,post =
    let (_,f) = get_node (juc,an) in
    let bhf = destr_bdHoareF f in
    bhf.bhf_pr, bhf.bhf_po in
  t_on_first (t_bdHoare_deno env pre post (juc,n)) (t_use env an gs)

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
    (* FIXME: Benjamin : below: put a better default event instead of f_true *)
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
      | FbdHoareF bhf ->
        let penv, qenv = EcEnv.Fun.hoareF bhf.bhf_f env in
        tac1, penv, qenv, bhf.bhf_pr, bhf.bhf_po, 
        (fun pre post -> f_bdHoareF pre bhf.bhf_f post bhf.bhf_cmp bhf.bhf_bd)
      | FbdHoareS bhs ->
        let env = EcEnv.Memory.push_active bhs.bhs_m env in
        tac1, env, env, bhs.bhs_pr, bhs.bhs_po,
        (fun pre post -> f_bdHoareS_r { bhs with bhs_pr = pre; bhs_po = post })
      | FequivF ef ->
        let penv, qenv = EcEnv.Fun.equivF ef.ef_fl ef.ef_fr env in
        tac2, penv, qenv, ef.ef_pr, ef.ef_po,
        (fun pre post -> f_equivF pre ef.ef_fl ef.ef_fr post)
      | FequivS es -> 
        let env = EcEnv.Memory.push_all [es.es_ml; es.es_mr] env in
        tac2, env, env, es.es_pr, es.es_po,
        (fun pre post -> f_equivS_r { es with es_pr = pre; es_po = post }) 
      | _ -> tacuerror "cannot apply conseq rule, not a phl/prhl judgement"
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
    | FbdHoareF hf -> t_bdHoareF_conseq env hf.bhf_pr hf.bhf_po
    | FbdHoareS hs -> t_bdHoareS_conseq env hs.bhs_pr hs.bhs_po
    | FequivF ef -> t_equivF_conseq env ef.ef_pr ef.ef_po
    | FequivS es -> t_equivS_conseq env es.es_pr es.es_po 
    | _ -> assert false (* FIXME error message *) in
  t_seq_subgoal t_conseq
    [!t_pre; !t_post; t_use env an gs] (juc,n)
  
let process_fun_abs env inv g =
  let concl = get_concl g in
  let env' = EcEnv.Fun.inv_memenv env in
  if is_equivS concl then
    let inv = process_prhl_formula env' g inv in
    t_equivF_abs env inv g
  else if is_bdHoareS concl then
    let inv = process_phl_formula env' g inv in
    t_bdHoareF_abs env inv g
  else if is_hoareS concl then
    let inv = process_phl_formula env' g inv in
    t_hoareF_abs env inv g
  else
    cannot_apply "fun" "equiv or probabilistic hoare triple was expected"
  
let process_fun_upto env (bad, p, o) g =
  let env' = EcEnv.Fun.inv_memenv env in 
  let p = process_prhl_formula env' g p in
  let q = 
    match o with
    | None -> EcFol.f_true
    | Some q -> process_prhl_formula env' g q in
  let bad = 
    let env =  EcEnv.Memory.push_active (EcFol.mhr,None) env in
    process_prhl_formula env g bad in
  t_equivF_abs_upto env bad p q g


let process_hoare_bd_hoare g = t_hoare_bd_hoare g
let process_prbounded = t_prbounded
let process_prfalse = t_prfalse
let process_pror = t_pror
let process_bdeq = t_bdeq


(* -------------------------------------------------------------------- *)
let process_phl loc env ptac g =
  let t =
    match ptac with
    | Pfun_def                 -> EcPhl.t_fun_def env
    | Pfun_abs f               -> process_fun_abs env f
    | Pfun_upto info           -> process_fun_upto env info 
    | Pskip                    -> EcPhl.t_skip
    | Papp (dir, k, phi, f)    -> process_app env dir k phi f
    | Pwp  k                   -> t_wp env k
    | Prcond (side, b, i)      -> t_rcond side b i
    | Pcond side               -> process_cond env side
    | Pwhile (phi, vopt, info) -> process_while env phi vopt info
    | Pfission info            -> process_fission env info
    | Pfusion info             -> process_fusion env info
    | Punroll info             -> process_unroll env info
    | Psplitwhile info         -> process_splitwhile env info
    | Pcall(side, (pre, post)) -> process_call env side pre post
    | Pswap info               -> process_swap env info
    | Pinline info             -> process_inline env info
    | Pkill info               -> process_kill env info
    | Palias info              -> process_alias env info
    | Prnd (side, info)        -> process_rnd side env info
    | Pconseq info             -> process_conseq env info
    | Pbdhoaredeno info        -> process_bdHoare_deno env info
    | Pequivdeno info          -> process_equiv_deno env info
    | Phoare | Pbdhoare        -> process_hoare_bd_hoare
    | Pprbounded               -> process_prbounded
    | Pprfalse                 -> process_prfalse env
    | Ppror                    -> process_pror
    | Pbdeq                    -> process_bdeq
  in
    set_loc loc t g
