(* -------------------------------------------------------------------- *)
open EcParsetree
open EcUtils
open EcIdent
open EcPath
open EcCoreLib
open EcTypes
open EcFol
open EcBaseLogic
open EcEnv
open EcPV
open EcLogic
open EcModules
open EcMetaProg

module Zpr = EcMetaProg.Zipper


(* -------------------------------------------------------------------- *)

let s_last destr_i error s =
  match List.rev s.s_node with
  | [] -> error ()
  | i :: r ->
    try destr_i i, rstmt r 
    with Not_found -> error ()

let s_lasts destr_i error sl sr =
  let hl,tl = s_last destr_i error sl in
  let hr,tr = s_last destr_i error sr in
  hl,hr,tl,tr

let last_error si st () = 
  cannot_apply st ("the last instruction should be a"^si)

let s_last_rnd     st = s_last  destr_rnd    (last_error " rnd" st)
let s_last_rnds    st = s_lasts destr_rnd    (last_error " rnd" st)
let s_last_call    st = s_last  destr_call   (last_error " call" st)
let s_last_calls   st = s_lasts destr_call   (last_error " call" st)
let s_last_if      st = s_last  destr_if     (last_error "n if" st)
let s_last_ifs     st = s_lasts destr_if     (last_error "n if" st)
let s_last_while   st = s_last  destr_while  (last_error " while" st)
let s_last_whiles  st = s_lasts destr_while  (last_error " while" st)
let s_last_assert  st = s_last  destr_assert (last_error "n assert" st)
let s_last_asserts st = s_lasts destr_assert (last_error "n assert" st)

(* -------------------------------------------------------------------- *)
(* -------------------------------  Wp -------------------------------- *)
(* -------------------------------------------------------------------- *)

let add_side name m = 
  let name = 
    if EcIdent.id_equal m mleft then name ^ "_L" 
    else if EcIdent.id_equal m mright then name ^ "_R"
    else name in
  EcIdent.create name       

let id_of_pv pv m =
  add_side (EcPath.basename pv.pv_name.EcPath.x_sub) m 

let id_of_mp mp m = 
  let name = 
    match mp.EcPath.m_top with
    | `Local id -> EcIdent.name id 
    | _ -> assert false in
  add_side name m

let generalize_mod env m modi f =
  let elts,glob = PV.elements modi in
  let create (pv,ty) = id_of_pv pv m, GTty ty in
  let b = List.map create elts in
  let s = List.fold_left2 (fun s (pv,ty) (id, _) ->
    PVM.add env pv m (f_local id ty) s) PVM.empty elts b in
  let create mp = id_of_mp mp m, GTty (tglob mp) in
  let b' = List.map create glob in
  let s = List.fold_left2 (fun s mp (id,_) ->
    PVM.add_glob env mp m (f_local id (tglob mp)) s) s glob b' in
  let f = PVM.subst env s f in
  f_forall_simpl (b'@b) f

let lv_subst m lv f =
  match lv with
  | LvVar(pv,t) ->
    let id = id_of_pv pv m in 
    (LSymbol (id,t), f), [pv,m,f_local id t]
  | LvTuple vs ->
    let ids = List.map (fun (pv,t) -> id_of_pv pv m, t) vs in
    let s = List.map2 (fun (pv,_) (id,t) -> pv,m,f_local id t) vs ids in
    (LTuple ids, f), s
  | LvMap((p,tys),pv,e,ty) ->
    let id = id_of_pv pv m in 
    let set = f_op p tys (toarrow [ty; e.e_ty; f.f_ty] ty) in
    let f = f_app set [f_pvar pv ty m; form_of_expr m e; f] ty in
    (LSymbol (id,ty), f), [pv,m,f_local id ty]
      
let wp_asgn_aux m lv e (lets,f) =
  let let1 = lv_subst m lv (form_of_expr m e) in
  (let1::lets,f)

exception HLerror

let mk_let env (lets,f) = 
  let rec aux s lets = 
    match lets with
    | [] -> PVM.subst env s f 
    | ((lp,f1), toadd) :: lets ->
      let f1 = PVM.subst env s f1 in
      let s = 
        List.fold_left (fun s (pv,m,fp) -> PVM.add env pv m fp s) s toadd in
      f_let_simpl lp f1 (aux s lets) in
  if lets = [] then f else aux PVM.empty lets 
  
exception No_wp

(* wp functions operate only over assignments and conditional statements.
   Any weakening on this restriction may break the soundness of bounded hoare logic 
*)
let rec wp_stmt env m (stmt: EcModules.instr list) letsf = 
  match stmt with
  | [] -> stmt, letsf
  | i :: stmt' -> 
      try 
        let letsf = wp_instr env m i letsf in
        wp_stmt env m stmt' letsf
      with No_wp -> stmt, letsf
and wp_instr env m i letsf = 
  match i.i_node with
  | Sasgn (lv,e) ->
      wp_asgn_aux m lv e letsf
  | Sif (e,s1,s2) -> 
      let r1,letsf1 = wp_stmt env m (List.rev s1.s_node) letsf in
      let r2,letsf2 = wp_stmt env m (List.rev s2.s_node) letsf in
      if r1=[] && r2=[] then
        let post1 = mk_let env letsf1 in 
        let post2 = mk_let env letsf2 in
        let post  = f_if (form_of_expr m e) post1 post2 in
        [], post
      else raise No_wp
  | _ -> raise No_wp

let wp env m s post = 
  let r,letsf = wp_stmt env m (List.rev s.s_node) ([],post) in
  List.rev r, mk_let env letsf 



(* let subst_form env m lv e f = *)
(*   let s = PVM.add env "pv" PVM.empty in *)
(*   mk_let env letsf *)

let subst_form_lv env m lv t f =
  let lets = lv_subst m lv t in
  mk_let env ([lets],f)

(* -------------------------------------------------------------------- *)
(* ----------------------  Auxiliary functions  ----------------------- *)
(* -------------------------------------------------------------------- *)

let destr_hoareF c =
  try destr_hoareF c with DestrError _ -> tacerror (NotPhl (Some true))
let destr_hoareS c =
  try destr_hoareS c with DestrError _ -> tacerror (NotPhl (Some true))
let destr_bdHoareF c =
  try destr_bdHoareF c with DestrError _ -> tacerror (NotPhl (Some true))
let destr_bdHoareS c =
  try destr_bdHoareS c with DestrError _ -> tacerror (NotPhl (Some true))
let destr_equivF c =
  try destr_equivF c with DestrError _ -> tacerror (NotPhl (Some false))
let destr_equivS c =
  try destr_equivS c with DestrError _ -> tacerror (NotPhl (Some false))

let t_hS_or_eS th te g =
  let concl = get_concl g in
  if is_hoareS concl then th g
  else if is_equivS concl then te g
  else tacerror (NotPhl None)

let t_hS_or_bhS th te g =
  let concl = get_concl g in
  if is_hoareS concl then th g
  else if is_bdHoareS concl then te g
  else tacerror (NotPhl None)

let t_hS_or_bhS_or_eS th tbh te g =
  let concl = get_concl g in
  if is_hoareS concl then th g
  else if is_bdHoareS concl then tbh g
  else if is_equivS concl then te g
  else tacerror (NotPhl None)

let prove_goal_by sub_gs rule (juc,n as g) =
  let hyps,_ = get_goal g in
  let add_sgoal (juc,ns) sg = 
    let juc,n = new_goal juc (hyps,sg) in juc, RA_node n::ns
  in
  let juc,ns = List.fold_left add_sgoal (juc,[]) sub_gs in
  let rule = { pr_name = rule ; pr_hyps = List.rev ns} in
  upd_rule rule (juc,n)

let gen_mems m f = 
  let bds = List.map (fun (m,mt) -> (m,GTmem mt)) m in
  f_forall bds f

let t_fold f env cpos _ (state, s) =
  try
    let (me, f) = Zpr.fold env cpos f state s in
      (me, f, [])
  with Zpr.InvalidCPos -> tacuerror "invalid code position"

let t_zip f env cpos prpo (state, s) =
  try
    let (me, zpr, gs) = f env prpo state (Zpr.zipper_of_cpos cpos s) in
      (me, Zpr.zip zpr, gs)
  with Zpr.InvalidCPos -> tacuerror "invalid code position"

let t_code_transform side ?(bdhoare = false) cpos tr tx g =
  match side with
  | None -> begin
      let hyps, concl = get_goal g in

      if is_hoareS concl then
        let hoare    = destr_hoareS concl in
        let pr, po   = hoare.hs_pr, hoare.hs_po in
        let (me, stmt, cs) = tx hyps cpos (pr, po) (hoare.hs_m, hoare.hs_s) in
        let concl = f_hoareS_r { hoare with hs_m = me; hs_s = stmt; } in
          prove_goal_by (cs @ [concl]) (tr None) g
      else if bdhoare && is_bdHoareS concl then
        let hoare    = destr_bdHoareS concl in
        let pr, po   = hoare.bhs_pr, hoare.bhs_po in
        let (me, stmt, cs) = tx hyps cpos (pr, po) (hoare.bhs_m, hoare.bhs_s) in
        let concl = f_bdHoareS_r { hoare with bhs_m = me; bhs_s = stmt; } in
          prove_goal_by (cs @ [concl]) (tr None) g
      else
        tacuerror "conclusion should be a hoare statement"
 end

  | Some side ->
      let hyps, concl  = get_goal g in
      let es        = destr_equivS concl in
      let pre, post = es.es_pr, es.es_po in
      let me, stmt     = if side then (es.es_ml, es.es_sl) else (es.es_mr, es.es_sr) in
      let me, stmt, cs = tx hyps cpos (pre, post) (me, stmt) in
      let concl =
        match side with
        | true  -> f_equivS_r { es with es_ml = me; es_sl = stmt; }
        | false -> f_equivS_r { es with es_mr = me; es_sr = stmt; }
      in
        prove_goal_by (cs @ [concl]) (tr (Some side)) g

(* -------------------------------------------------------------------- *)
(* -------------------------  Tactics --------------------------------- *)
(* -------------------------------------------------------------------- *)

(* {spre} . {spost}     pre => spre  spost => post
   --------------------------------------------------
       {pre} . {post} 
*)
let conseq_cond pre post spre spost = 
  f_imp pre spre, f_imp spost post
 
let t_hoareF_conseq pre post g =
  let env,_,concl = get_goal_e g in
  let hf = destr_hoareF concl in
  let mpr,mpo = EcEnv.Fun.hoareF_memenv hf.hf_f env in
  let cond1, cond2 = conseq_cond hf.hf_pr hf.hf_po pre post in
  let concl1 = gen_mems [mpr] cond1 in
  let concl2 = gen_mems [mpo] cond2 in
  let concl3 = f_hoareF pre hf.hf_f post in
  prove_goal_by [concl1; concl2; concl3] (RN_hl_conseq) g  
    
let t_hoareS_conseq pre post g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  let cond1, cond2 = conseq_cond hs.hs_pr hs.hs_po pre post in
  let concl1 = gen_mems [hs.hs_m] cond1 in
  let concl2 = gen_mems [hs.hs_m] cond2 in
  let concl3 = f_hoareS_r { hs with hs_pr = pre; hs_po = post } in
  prove_goal_by [concl1; concl2; concl3] (RN_hl_conseq) g

let t_bdHoareF_conseq pre post g =
  let env,_,concl = get_goal_e g in
  let bhf = destr_bdHoareF concl in
  let mpr,mpo = EcEnv.Fun.hoareF_memenv bhf.bhf_f env in
  let cond1, cond2 = conseq_cond bhf.bhf_pr bhf.bhf_po pre post in
  let cond2 = match bhf.bhf_cmp with
    | FHle -> f_imp bhf.bhf_po post
    | FHeq -> f_iff bhf.bhf_po post
    | FHge -> cond2
  in
  let concl1 = gen_mems [mpr] cond1 in
  let concl2 = gen_mems [mpo] cond2 in
  let concl3 = f_bdHoareF pre bhf.bhf_f post bhf.bhf_cmp bhf.bhf_bd in
  prove_goal_by [concl1; concl2; concl3] (RN_hl_conseq) g  

let t_bdHoareS_conseq pre post g =
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in
  let cond1, cond2 = conseq_cond bhs.bhs_pr bhs.bhs_po pre post in
  let cond2 = match bhs.bhs_cmp with
    | FHle -> f_imp bhs.bhs_po post
    | FHeq -> f_iff bhs.bhs_po post
    | FHge -> cond2
  in
  let concl1 = gen_mems [bhs.bhs_m] cond1 in
  let concl2 = gen_mems [bhs.bhs_m] cond2 in
  let concl3 = f_bdHoareS_r { bhs with bhs_pr = pre; bhs_po = post } in
  prove_goal_by [concl1; concl2; concl3] (RN_hl_conseq) g

let t_equivF_conseq pre post g =
  let env,_,concl = get_goal_e g in
  let ef = destr_equivF concl in
  let (mprl,mprr),(mpol,mpor) = 
    EcEnv.Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
  let cond1, cond2 = conseq_cond ef.ef_pr ef.ef_po pre post in
  let concl1 = gen_mems [mprl;mprr] cond1 in
  let concl2 = gen_mems [mpol;mpor] cond2 in
  let concl3 = f_equivF pre ef.ef_fl ef.ef_fr post in
  prove_goal_by [concl1; concl2; concl3] (RN_hl_conseq) g  

let t_equivS_conseq pre post g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  let cond1, cond2 = conseq_cond es.es_pr es.es_po pre post in
  let concl1 = gen_mems [es.es_ml;es.es_mr] cond1 in
  let concl2 = gen_mems [es.es_ml;es.es_mr] cond2 in
  let concl3 = f_equivS_r { es with es_pr = pre; es_po = post } in
  prove_goal_by [concl1; concl2; concl3] (RN_hl_conseq) g

(* -------------------------------------------------------------------- *)

let t_hoareF_exfalso g =
  let concl = get_concl g in
  let hf = destr_hoareF concl in
  if hf.hf_pr <> f_false then tacerror InvalidExfalso;
  prove_goal_by [] (RN_hl_exfalso) g

let t_hoareS_exfalso g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  if hs.hs_pr <> f_false then tacerror InvalidExfalso;
  prove_goal_by [] (RN_hl_exfalso) g

let t_bdHoareF_exfalso g =
  let concl = get_concl g in
  let bhf = destr_bdHoareF concl in
  if bhf.bhf_pr <> f_false then tacerror InvalidExfalso;
  prove_goal_by [] (RN_hl_exfalso) g

let t_bdHoareS_exfalso g =
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in
  if bhs.bhs_pr <> f_false then tacerror InvalidExfalso;
  prove_goal_by [] (RN_hl_exfalso) g

let t_equivF_exfalso g =
  let concl = get_concl g in
  let ef = destr_equivF concl in
  if ef.ef_pr <> f_false then tacerror InvalidExfalso;
  prove_goal_by [] (RN_hl_exfalso) g

let t_equivS_exfalso g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  if es.es_pr <> f_false then tacerror InvalidExfalso;
  prove_goal_by [] (RN_hl_exfalso) g

(* -------------------------------------------------------------------- *)

let t_hoareF_fun_def g = 
  let env,_,concl = get_goal_e g in
  let hf = destr_hoareF concl in
  let memenv, fdef, env = Fun.hoareS hf.hf_f env in (* FIXME catch exception *)
  let m = EcMemory.memory memenv in
  let fres = 
    match fdef.f_ret with
    | None -> f_tt
    | Some e -> form_of_expr m e in
  let post = PVM.subst1 env (pv_res hf.hf_f) m fres hf.hf_po in
  let concl' = f_hoareS memenv hf.hf_pr fdef.f_body post in
  prove_goal_by [concl'] RN_hl_fun_def g

let t_bdHoareF_fun_def g = 
  let env,_,concl = get_goal_e g in
  let bhf = destr_bdHoareF concl in
  let memenv, fdef, env = Fun.hoareS bhf.bhf_f env in(* FIXME catch exception *)
  let m = EcMemory.memory memenv in
  let fres = 
    match fdef.f_ret with
    | None -> f_tt
    | Some e -> form_of_expr m e in
  let post = PVM.subst1 env (pv_res bhf.bhf_f) m fres bhf.bhf_po in
  let concl' = f_bdHoareS memenv bhf.bhf_pr fdef.f_body post bhf.bhf_cmp bhf.bhf_bd  in
  prove_goal_by [concl'] RN_hl_fun_def g


let t_equivF_fun_def g = 
  let env,_,concl = get_goal_e g in
  let ef = destr_equivF concl in
  let memenvl,fdefl,memenvr,fdefr,env = Fun.equivS ef.ef_fl ef.ef_fr env in 
                                (* FIXME catch exception *)
  let ml, mr = EcMemory.memory memenvl, EcMemory.memory memenvr in
  let fresl = 
    match fdefl.f_ret with
    | None -> f_tt
    | Some e -> form_of_expr ml e in
  let fresr = 
    match fdefr.f_ret with
    | None -> f_tt
    | Some e -> form_of_expr mr e in
  let s = PVM.add env (pv_res ef.ef_fl) ml fresl PVM.empty in
  let s = PVM.add env (pv_res ef.ef_fr) mr fresr s in
  let post = PVM.subst env s ef.ef_po in
  let concl' = 
    f_equivS memenvl memenvr ef.ef_pr fdefl.f_body fdefr.f_body post in
  
  prove_goal_by [concl'] RN_hl_fun_def g


let t_fun_def g =
  let concl = get_concl g in
  if is_hoareF concl then t_hoareF_fun_def g
  else if is_bdHoareF concl then t_bdHoareF_fun_def g
  else if is_equivF concl then t_equivF_fun_def g
  else tacerror (NotPhl None)

  
(* TODO FIXME : oracle should ensure that the adversary state still equal:
   two solutions : 
     - add the equality in the pre and post.
     - ensure that oracle do not write the adversary state
 *)


let abstract_info env f1 = 
  let f = EcEnv.NormMp.norm_xpath env f1 in
  let top = EcPath.m_functor f.EcPath.x_top in
  let def = EcEnv.Fun.by_xpath f env in
  let oi = 
    match def.f_def with
    | FBabs oi -> oi
    | _ -> 
      let ppe = EcPrinting.PPEnv.ofenv env in
      if EcPath.x_equal f1 f then 
        EcLogic.tacuerror "The function %a should be abstract"
          (EcPrinting.pp_funname ppe) f1
      else 
        EcLogic.tacuerror 
          "The function %a, which reduce to %a, should be abstract"
          (EcPrinting.pp_funname ppe) f1
          (EcPrinting.pp_funname ppe) f in
  top, f, oi, def.f_sig


let hoareF_abs_spec env f inv = 
  let top, _, oi, _fsig = abstract_info env f in
  let m = mhr in
  let fv = PV.fv env m inv in
  PV.check_depend env fv top;
  let ospec o = f_hoareF inv o inv in
  let sg = List.map ospec oi.oi_calls in
  inv, inv, sg

let t_hoareF_abs inv g = 
  let env,_,concl = get_goal_e g in
  let hf = destr_hoareF concl in
  let pre, post, sg = hoareF_abs_spec env hf.hf_f inv in
  let tac g' = prove_goal_by sg (RN_hl_fun_abs inv) g' in
  t_on_last tac (t_hoareF_conseq pre post g)

let lossless_hyps env top sub = 
  let sig_ = (EcEnv.Mod.by_mpath top env).me_sig in
  let bd = 
    List.map (fun (id,mt) -> id,GTmodty(mt,EcPath.Sm.empty))
      sig_.mis_params in               (* Should we put restriction here *)
  let args = List.map (fun (id,_) -> EcPath.mident id) sig_.mis_params in
  let concl = 
    f_losslessF (EcPath.xpath (EcPath.m_apply top args) sub) in
  let calls = 
    let name = EcPath.basename sub in
    let Tys_function(_,oi) = 
      List.find (fun (Tys_function(fs,_)) -> fs.fs_name = name)
        sig_.mis_body in
    oi.oi_calls in
  let hyps = List.map f_losslessF calls in
  f_forall bd (f_imps hyps concl) 

let bdHoareF_abs_spec env f inv = 
  let top,_,oi,_fsig = abstract_info env f in
  let m = mhr in
  let fv = PV.fv env m inv in
  PV.check_depend env fv top;
  let ospec o = f_bdHoareF inv o inv FHeq f_r1 in
  let sg = List.map ospec oi.oi_calls in
  inv, inv, lossless_hyps env top f.x_sub :: sg

let t_bdHoareF_abs inv g = 
  let env,_,concl = get_goal_e g in
  let bhf = destr_bdHoareF concl in
  match bhf.bhf_cmp with
    | FHeq when f_equal bhf.bhf_bd f_r1 -> 
      let pre, post, sg = bdHoareF_abs_spec env bhf.bhf_f inv in
      let tac g' = prove_goal_by sg (RN_hl_fun_abs inv) g' in
      t_on_last tac (t_bdHoareF_conseq pre post g)
    | _ ->
      cannot_apply "fun" "expected \"= 1\" as bound"

let abstract_info2 env fl' fr' =
  let topl, fl, oil, sigl = abstract_info env fl' in
  let topr, fr, oir, sigr = abstract_info env fr' in
  let fl1 = EcPath.xpath topl fl.x_sub in
  let fr1 = EcPath.xpath topr fr.x_sub in
  if not (EcPath.x_equal fl1 fr1) then
    let ppe = EcPrinting.PPEnv.ofenv env in
    EcLogic.tacuerror 
      "function %a reduce to %a and %a reduce to %a, %a and %a should be equal"
      (EcPrinting.pp_funname ppe) fl'
      (EcPrinting.pp_funname ppe) fl1
      (EcPrinting.pp_funname ppe) fr'
      (EcPrinting.pp_funname ppe) fr1
      (EcPrinting.pp_funname ppe) fl1
      (EcPrinting.pp_funname ppe) fr1
  else 
    topl, fl, oil, sigl, topr, fr, oir, sigr

let check_wr env needed top o_l o_r = 
  let wl,wr = f_write env o_l, f_write env o_r in
  let rl,rr = f_read env o_l, f_read env o_r in
  let trl = PV.mem_glob env top rl in
  let trr = PV.mem_glob env top rr in
  let twl = PV.mem_glob env top wl in
  let twr = PV.mem_glob env top wr in
  if not needed then begin
    let error f msg = 
      let ppe = EcPrinting.PPEnv.ofenv env in
      EcLogic.tacuerror "The function %a should not %s variables of %a"
        (EcPrinting.pp_funname ppe) f msg
        (EcPrinting.pp_topmod ppe) top in
    if trl then error o_l "read";
    if trr then error o_r "read";
    if twl then error o_l "write";
    if twr then error o_r "write"
  end;
  trl || trr, twl || twr
        
let equivF_abs_spec env fl fr inv = 
  let topl, fl, oil,sigl, topr, fr, oir,sigr = abstract_info2 env fl fr in
  let ml, mr = mleft, mright in
  let fvl = PV.fv env ml inv in
  let fvr = PV.fv env mr inv in
  PV.check_depend env fvl topl;
  PV.check_depend env fvr topr;
  let eqglob = f_eqglob topl ml topr mr in

  let ospec o_l o_r = 
    let w,r = check_wr env oil.oi_in topl o_l o_r in
    let fo_l = EcEnv.Fun.by_xpath o_l env in
    let fo_r = EcEnv.Fun.by_xpath o_r env in
    let eq_params = 
      f_eqparams o_l fo_l.f_sig.fs_params ml o_r fo_r.f_sig.fs_params mr in
    let eq_res = f_eqres o_l fo_l.f_sig.fs_ret ml o_r fo_r.f_sig.fs_ret mr in
    (* TODO : Did we really want this eqglob, or just that oracle do not 
              modify glob ? *)  
    let lpre = if oil.oi_in && (w||r) then [eqglob;inv] else [inv] in
    let pre = EcFol.f_ands (eq_params::lpre) in
    let lpost = if w then [eqglob;inv] else [inv] in
    let post = EcFol.f_ands (eq_res::lpost) in
    f_equivF pre o_l o_r post in
  let sg = List.map2 ospec oil.oi_calls oir.oi_calls in
  let eq_params = 
    f_eqparams fl sigl.fs_params ml fr sigr.fs_params mr in
  let eq_res = f_eqres fl sigl.fs_ret ml fr sigr.fs_ret mr in
  let lpre = if oil.oi_in then [eqglob;inv] else [inv] in
  let pre = f_ands (eq_params::lpre) in
  let post = f_ands [eq_res; eqglob; inv] in
  pre, post, sg

let t_equivF_abs inv g = 
  let env,_,concl = get_goal_e g in
  let ef = destr_equivF concl in
  let pre, post, sg = equivF_abs_spec env ef.ef_fl ef.ef_fr inv in
  let tac g' = prove_goal_by sg (RN_hl_fun_abs inv) g' in
  t_on_last tac (t_equivF_conseq pre post g)

let equivF_abs_upto env fl fr bad invP invQ = 
  let topl, fl, oil,sigl, topr, fr, oir,sigr = abstract_info2 env fl fr in
  let ml, mr = mleft, mright in
  let bad2 = Fsubst.f_subst_mem mhr mr bad in
  let allinv = f_ands [bad2; invP; invQ] in
  let fvl = PV.fv env ml allinv in
  let fvr = PV.fv env mr allinv in
  PV.check_depend env fvl topl;
  PV.check_depend env fvr topr;
  (* TODO check there is only global variable *)
  let eqglob = f_eqglob topl ml topr mr in

  let ospec o_l o_r = 
    let w,r = check_wr env oil.oi_in topl o_l o_r in
    let fo_l = EcEnv.Fun.by_xpath o_l env in
    let fo_r = EcEnv.Fun.by_xpath o_r env in
    let eq_params = 
      f_eqparams o_l fo_l.f_sig.fs_params ml o_r fo_r.f_sig.fs_params mr in
    let eq_res = f_eqres o_l fo_l.f_sig.fs_ret ml o_r fo_r.f_sig.fs_ret mr in
    let lpre = if oil.oi_in && (w||r) then [eqglob;invP] else [invP] in
    let pre = EcFol.f_ands (EcFol.f_not bad2 :: eq_params :: lpre) in
    let lpost = if w then [eqglob;invP] else [invP] in
    let post = EcFol.f_if_simpl bad2 invQ (f_ands (eq_res::lpost)) in
    let cond1 = f_equivF pre o_l o_r post in
    let cond2 =
      let q = Fsubst.f_subst_mem ml EcFol.mhr invQ in
      f_forall [mr,GTmem None] (f_imp bad2 (f_bdHoareF q o_l q FHeq f_r1)) in
    let cond3 = 
      let q = Fsubst.f_subst_mem mr EcFol.mhr invQ in
      let bq = f_and bad q in
      f_forall [ml,GTmem None] (f_bdHoareF bq o_r bq FHeq f_r1) in
    [cond1;cond2;cond3] in
  let sg = List.map2 ospec oil.oi_calls oir.oi_calls in
  let sg = List.flatten sg in
  let lossless_a = lossless_hyps env topl fl.x_sub in
  let sg = lossless_a :: sg in
  let eq_params = 
    f_eqparams fl sigl.fs_params ml fr sigr.fs_params mr in
  let eq_res = f_eqres fl sigl.fs_ret ml fr sigr.fs_ret mr in
  let lpre = if oil.oi_in then [eqglob;invP] else [invP] in
  let pre = f_if_simpl bad2 invQ (f_ands (eq_params::lpre)) in
  let post = f_if_simpl bad2 invQ (f_ands [eq_res;eqglob;invP]) in
  pre, post, sg

let t_equivF_abs_upto bad invP invQ g = 
  let env,_,concl = get_goal_e g in
  let ef = destr_equivF concl in
  let pre, post, sg = equivF_abs_upto env ef.ef_fl ef.ef_fr bad invP invQ in
  let tac g' = prove_goal_by sg (RN_hl_fun_upto(bad,invP,invQ)) g' in
  t_on_last tac (t_equivF_conseq pre post g)

(* -------------------------------------------------------------------- *)  
let t_hoare_skip g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  if hs.hs_s.s_node <> [] then tacerror NoSkipStmt;
  let concl = f_imp hs.hs_pr hs.hs_po in
  let concl = gen_mems [hs.hs_m] concl in
  prove_goal_by [concl] RN_hl_skip g

let t_bdHoare_skip g =
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in
  if bhs.bhs_s.s_node <> [] then tacerror NoSkipStmt;
  if (bhs.bhs_cmp <> FHeq && bhs.bhs_cmp <> FHge) then
    cannot_apply "skip" "bound must be \">= 1\"";
  let eq_to_one = f_eq bhs.bhs_bd f_r1 in
  let concl = f_imp bhs.bhs_pr bhs.bhs_po in
  let concl = gen_mems [bhs.bhs_m] concl in
  prove_goal_by [eq_to_one;concl] RN_hl_skip g

let t_equiv_skip g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  if es.es_sl.s_node <> [] then tacerror NoSkipStmt;
  if es.es_sr.s_node <> [] then tacerror NoSkipStmt;
  let concl = f_imp es.es_pr es.es_po in
  let concl = gen_mems [es.es_ml; es.es_mr] concl in
  prove_goal_by [concl] RN_hl_skip g

let t_skip = 
  t_hS_or_bhS_or_eS t_hoare_skip t_bdHoare_skip t_equiv_skip 

(* -------------------------------------------------------------------- *)

let s_split_i msg i s = 
  let len = List.length s.s_node in
  if not (0 < i && i <= len) then tacerror (InvalidCodePosition (msg,i,1,len));
  let hd,tl = s_split (i-1) s in
  hd, List.hd tl, (List.tl tl)

let s_split msg i s =
  let len = List.length s.s_node in
  if i < 0 ||  len < i then tacerror (InvalidCodePosition (msg,i,0,len))
  else s_split i s

let s_split_o msg i s = 
  match i with
  | None -> [], s.s_node
  | Some i -> s_split msg i s 

(* -------------------------------------------------------------------- *)

let t_hoare_app i phi g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  let s1,s2 = s_split "app" i hs.hs_s in
  let a = f_hoareS_r { hs with hs_s = stmt s1; hs_po = phi }  in
  let b = f_hoareS_r { hs with hs_pr = phi; hs_s = stmt s2 } in
  prove_goal_by [a;b] (RN_hl_append (Backs,Single i,phi,AppNone)) g

let t_bdHoare_app dir i phi bd_info g =
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in
  let s1,s2 = s_split "app" i bhs.bhs_s in
  match bd_info, bhs.bhs_cmp with
    | AppNone, FHle when dir=Backs ->
      let a = f_hoareS bhs.bhs_m bhs.bhs_pr (stmt s1) phi in
      let b = f_bdHoareS_r { bhs with bhs_pr = phi; bhs_s = stmt s2} in
      prove_goal_by [a;b] (RN_hl_append (dir, Single i,phi,bd_info)) g
    | AppMult (f1,f2,g1,g2), FHle ->
      let a1 = f_bdHoareS_r { bhs with bhs_po = phi; bhs_s = stmt s1; bhs_bd=f1}  in
      let b1 = f_bdHoareS_r { bhs with bhs_pr = phi; bhs_s = stmt s2; bhs_bd=f2} in
      let a2 = f_bdHoareS_r { bhs with bhs_po = f_not phi; bhs_s = stmt s1; bhs_bd=g1}  in
      let b2 = f_bdHoareS_r { bhs with bhs_pr = f_not phi; bhs_s = stmt s2; bhs_bd=g2} in
      let bd_g = f_real_le (f_real_sum (f_real_prod f1 f2) (f_real_prod g1 g2)) bhs.bhs_bd in
      prove_goal_by [a1;b1;a2;b2;bd_g] (RN_hl_append (dir, Single i,phi,bd_info)) g

    | _, FHle when dir <>Backs -> 
      cannot_apply "app" 
        "forward direction not supported with upper bounded Hoare judgments "
      
    | AppSingle _ , FHle ->
      cannot_apply "app" 
        "single optional bound parameter not supported with upper bounded Hoare judgments"

    | AppSingle bd, FHeq | AppSingle bd, FHge ->
      let bd1,bd2,cmp1,cmp2 = 
        if dir=Backs then f_real_div_simpl bhs.bhs_bd bd, bd, bhs.bhs_cmp, bhs.bhs_cmp
        else bd, f_real_div_simpl bhs.bhs_bd bd, bhs.bhs_cmp, bhs.bhs_cmp
      in
      let a = f_bdHoareS_r { bhs with bhs_s = stmt s1; bhs_po = phi; 
        bhs_bd = bd1; bhs_cmp = cmp1 } in
      let b = f_bdHoareS_r { bhs with bhs_pr = phi; bhs_s = stmt s2;
        bhs_bd = bd2; bhs_cmp = cmp2 } in
      prove_goal_by [a;b] (RN_hl_append (dir, Single i,phi,bd_info)) g

    | AppNone, _ -> 
      let bd1,bd2,cmp1,cmp2 = 
        if dir=Backs then f_r1, bhs.bhs_bd, FHeq, bhs.bhs_cmp
        else bhs.bhs_bd, f_r1, bhs.bhs_cmp, FHeq
      in
      let a = f_bdHoareS_r { bhs with bhs_s = stmt s1; bhs_po = phi; 
        bhs_bd = bd1; bhs_cmp = cmp1 } in
      let b = f_bdHoareS_r { bhs with bhs_pr = phi; bhs_s = stmt s2;
        bhs_bd = bd2; bhs_cmp = cmp2 } in
      prove_goal_by [a;b] (RN_hl_append (dir, Single i,phi,bd_info)) g
      
    | AppMult _, _ ->
      cannot_apply "app" 
        "multiple bound parameters not supported with lower bounded and exact Hoare judgments"



let t_equiv_app (i,j) phi g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  let sl1,sl2 = s_split "app" i es.es_sl in
  let sr1,sr2 = s_split "app" j es.es_sr in
  let a = f_equivS_r {es with es_sl=stmt sl1; es_sr=stmt sr1; es_po=phi} in
  let b = f_equivS_r {es with es_pr=phi; es_sl=stmt sl2; es_sr=stmt sr2} in
  prove_goal_by [a;b] (RN_hl_append (Backs,Double (i,j), phi,AppNone)) g

  
(* -------------------------------------------------------------------- *)


let check_wp_progress msg i s remain =
  match i with
  | None -> List.length s.s_node - List.length remain
  | Some i ->
    let len = List.length remain in
    if len = 0 then i
    else
      cannot_apply msg 
        (Format.sprintf "remaining %i instruction%s" len 
           (if len = 1 then "" else "s"))

let t_hoare_wp i g =
  let env,_,concl = get_goal_e g in
  let hs = destr_hoareS concl in
  let s_hd,s_wp = s_split_o "wp" i hs.hs_s in
  let s_wp,post = 
    wp env (EcMemory.memory hs.hs_m) (EcModules.stmt s_wp) hs.hs_po in
  let i = check_wp_progress "wp" i hs.hs_s s_wp in
  let s = EcModules.stmt (s_hd @ s_wp) in
  let concl = f_hoareS_r { hs with hs_s = s; hs_po = post} in
  prove_goal_by [concl] (RN_hl_wp (Single i)) g

let t_bdHoare_wp i g =
  let env,_,concl = get_goal_e g in
  let bhs = destr_bdHoareS concl in
  let s_hd,s_wp = s_split_o "wp" i bhs.bhs_s in
  let s_wp = EcModules.stmt s_wp in

  let m = EcMemory.memory bhs.bhs_m in

  let fv_bd = PV.fv env m bhs.bhs_bd in
  let modi = s_write env s_wp in

  if not (PV.indep env fv_bd modi) then 
    cannot_apply "wp" "Not_implemented: bound is modified by the statement";

  let s_wp,post = 
    wp env m s_wp bhs.bhs_po in
  let i = check_wp_progress "wp" i bhs.bhs_s s_wp in
  let s = EcModules.stmt (s_hd @ s_wp) in
  let concl = f_bdHoareS_r { bhs with bhs_s = s; bhs_po = post} in
  prove_goal_by [concl] (RN_hl_wp (Single i)) g


let t_equiv_wp ij g = 
  let env,_,concl = get_goal_e g in
  let es = destr_equivS concl in
  let i = omap ij fst and j = omap ij snd in
  let s_hdl,s_wpl = s_split_o "wp" i es.es_sl in
  let s_hdr,s_wpr = s_split_o "wp" j es.es_sr in
  let s_wpl,post = 
    wp env (EcMemory.memory es.es_ml) (EcModules.stmt s_wpl) es.es_po in
  let s_wpr, post =
    wp env (EcMemory.memory es.es_mr) (EcModules.stmt s_wpr) post in
  let i = check_wp_progress "wp" i es.es_sl s_wpl in
  let j = check_wp_progress "wp" j es.es_sr s_wpr in
  let sl = EcModules.stmt (s_hdl @ s_wpl) in
  let sr = EcModules.stmt (s_hdr @ s_wpr) in
  let concl = f_equivS_r {es with es_sl = sl; es_sr=sr; es_po = post} in
  prove_goal_by [concl] (RN_hl_wp (Double(i,j))) g


let t_wp k = match k with
  | None -> 
    t_hS_or_bhS_or_eS (t_hoare_wp None) (t_bdHoare_wp None) (t_equiv_wp None)
  | Some (Single i) -> t_hS_or_bhS (t_hoare_wp (Some i)) (t_bdHoare_wp (Some i))
  | Some (Double(i,j)) -> t_equiv_wp (Some (i,j))


(* -------------------------------------------------------------------- *)
  
let t_hoare_while inv g =
  let env, _, concl = get_goal_e g in
  let hs = destr_hoareS concl in
  let ((e,c),s) = s_last_while "while" hs.hs_s in
  let m = EcMemory.memory hs.hs_m in
  let e = form_of_expr m e in
      (* the body preserve the invariant *)
  let b_pre  = f_and_simpl inv e in
  let b_post = inv in
  let b_concl = f_hoareS hs.hs_m b_pre c b_post in
      (* the wp of the while *)
  let post = f_imps_simpl [f_not_simpl e; inv] hs.hs_po in
  let modi = s_write env c in
  let post = generalize_mod env m modi post in
  let post = f_and_simpl inv post in
  let concl = f_hoareS_r { hs with hs_s = s; hs_po=post} in
  prove_goal_by [b_concl;concl] (RN_hl_while (inv,None,None)) g

let t_bdHoare_while inv vrnt info g =
  let env, _, concl = get_goal_e g in
  let bhs = destr_bdHoareS concl in
  let ((e,c),s) = s_last_while "while" bhs.bhs_s in
  let m = EcMemory.memory bhs.bhs_m in
  let e = form_of_expr m e in
  match info with 
    | None ->
      (* the body preserve the invariant *)
      let k_id = EcIdent.create "z" in
      let k = f_local k_id tint in
      let vrnt_eq_k = f_eq vrnt k in
      let vrnt_lt_k = f_int_lt vrnt k in
      let b_pre  = f_and_simpl (f_and_simpl inv e) vrnt_eq_k in
      let b_post = f_and_simpl inv vrnt_lt_k in
      let b_concl = f_bdHoareS_r 
        { bhs with bhs_pr=b_pre; bhs_s=c; bhs_po=b_post;
          bhs_cmp=FHeq; bhs_bd=f_r1} 
      in
      let b_concl = f_forall_simpl [(k_id,GTty tint)] b_concl in
      (* the wp of the while *)
      let post = f_imps_simpl [f_not_simpl e; inv] bhs.bhs_po in
      let term_condition = f_imps_simpl [inv;f_int_le vrnt (f_int 0)] (f_not_simpl e) in
      let post = f_and term_condition post in
      let modi = s_write env c in
      let post = generalize_mod env m modi post in
      let post = f_and_simpl inv post in
      let concl = f_bdHoareS_r { bhs with bhs_s = s; bhs_po=post} in
      prove_goal_by [b_concl;concl] (RN_hl_while (inv,Some vrnt, info)) g
    | _ ->
      cannot_apply "while" "not implemented"

let t_equiv_while_disj side vrnt inv g =
  let env, _, concl = get_goal_e g in
  let es = destr_equivS concl in
  let s,m_side,m_other = if side then es.es_sl, es.es_ml, es.es_mr 
    else es.es_sr, es.es_mr, es.es_ml in
  let ((e,c),s) = s_last_while "while" s in
  let e = form_of_expr (EcMemory.memory m_side) e in
  (* the body preserve the invariant and variant decreases *)
  let k_id = EcIdent.create "z" in
  let k = f_local k_id tint in
  let vrnt_eq_k = f_eq vrnt k in
  let vrnt_lt_k = f_int_lt vrnt k in
  let m_other' = EcIdent.create "&m",EcMemory.memtype m_other in
  let smem = Fsubst.f_bind_mem Fsubst.f_subst_id (EcMemory.memory m_side) mhr in
  let smem = Fsubst.f_bind_mem smem (EcMemory.memory m_other) (EcMemory.memory m_other') in
  let b_pre  = f_and_simpl (f_and_simpl inv e) vrnt_eq_k in
  let b_pre = Fsubst.f_subst smem b_pre in
  let b_post = f_and_simpl inv vrnt_lt_k in
  let b_post = Fsubst.f_subst smem b_post in
  let b_concl = f_bdHoareS (mhr,EcMemory.memtype m_side) b_pre c b_post FHeq f_r1 in 
  let b_concl = f_forall_simpl [(k_id,GTty tint)] b_concl in
  let b_concl = gen_mems [m_other'] b_concl in
      (* the wp of the while *)
  let post = f_imps_simpl [f_not_simpl e; inv] es.es_po in
  let term_condition = f_imps_simpl [inv;f_int_le vrnt (f_int 0)] (f_not_simpl e) in
  let post = f_and term_condition post in
  let modi = s_write env c in
  let post = generalize_mod env (EcMemory.memory m_side) modi post in
  let post = f_and_simpl inv post in
  let concl = if side then f_equivS_r { es with es_sl = s; es_po=post}
    else f_equivS_r { es with es_sr = s; es_po=post} in
  prove_goal_by [b_concl;concl] (RN_hl_while (inv,Some vrnt, None)) g

let t_equiv_while inv g =
  let env,_,concl = get_goal_e g in
  let es = destr_equivS concl in
  let (el,cl), (er,cr), sl, sr = s_last_whiles "while" es.es_sl es.es_sr in
  let ml = EcMemory.memory es.es_ml in
  let mr = EcMemory.memory es.es_mr in
  let el = form_of_expr ml el in
  let er = form_of_expr mr er in
  let sync_cond = f_iff_simpl el er in
      (* the body preserve the invariant *)
  let b_pre  = f_ands_simpl [inv; el] er in
  let b_post = f_and_simpl inv sync_cond in
  let b_concl = f_equivS es.es_ml es.es_mr b_pre cl cr b_post in
      (* the wp of the while *)
  let post = f_imps_simpl [f_not_simpl el;f_not_simpl er; inv] es.es_po in
  let modil = s_write env cl in
  let modir = s_write env cr in
  let post = generalize_mod env mr modir post in
  let post = generalize_mod env ml modil post in
  let post = f_and_simpl inv post in
  let concl = f_equivS_r {es with es_sl = sl; es_sr = sr; es_po = post} in
  prove_goal_by [b_concl; concl] (RN_hl_while (inv,None,None)) g 

(* -------------------------------------------------------------------- *)

let wp_asgn_call env m lv res post =
  match lv with
  | None -> post
  | Some lv ->
    let lets = lv_subst m lv res in
    mk_let env ([lets],post)

let subst_args_call env m f =
  List.fold_right2 (fun v e s ->
    PVM.add env (pv_loc f v.v_name) m (form_of_expr m e) s)
  
let t_hoare_call fpre fpost g =
  (* FIXME : check the well formess of the pre and the post ? *)
  let env,_,concl = get_goal_e g in
  let hs = destr_hoareS concl in
  let (lp,f,args),s = s_last_call "call" hs.hs_s in
  let m = EcMemory.memory hs.hs_m in
  let fsig = (Fun.by_xpath f env).f_sig in
  (* The function satisfies the specification *)
  let f_concl = f_hoareF fpre f fpost in
  (* The wp *)
  let pvres = pv_res f in
  let vres = EcIdent.create "result" in
  let fres = f_local vres fsig.fs_ret in
  let post = wp_asgn_call env m lp fres hs.hs_po in
  let fpost = PVM.subst1 env pvres m fres fpost in 
  let modi = f_write env f in
  let post = generalize_mod env m modi (f_imp_simpl fpost post) in
  let post = f_forall_simpl [(vres, GTty fsig.fs_ret)] post in
  let spre = subst_args_call env m f fsig.fs_params args PVM.empty in
  let post = f_anda_simpl (PVM.subst env spre fpre) post in
  let concl = f_hoareS_r { hs with hs_s = s; hs_po=post} in
  prove_goal_by [f_concl;concl] (RN_hl_call (None, fpre, fpost)) g


let bdHoare_call_spec fpre fpost f cmp bd opt_bd = 
  match cmp, opt_bd with
  | FHle, Some _ -> cannot_apply "call" 
    "optional bound parameter not allowed for upper-bounded judgements"
  | FHle, None -> 
    f_bdHoareF fpre f fpost FHle bd 
  | FHeq, Some bd ->
    f_bdHoareF fpre f fpost FHeq bd 
  | FHeq, None -> 
    f_bdHoareF fpre f fpost FHeq bd 
  | FHge, Some bd -> 
    f_bdHoareF fpre f fpost FHge bd 
  | FHge, None -> 
    f_bdHoareF fpre f fpost FHge bd 
  
let t_bdHoare_call fpre fpost opt_bd g =
  (* FIXME : check the well formess of the pre and the post ? *)
  let env,_,concl = get_goal_e g in
  let bhs = destr_bdHoareS concl in
  let (lp,f,args),s = s_last_call "call" bhs.bhs_s in
  let m = EcMemory.memory bhs.bhs_m in
  let fsig = (Fun.by_xpath f env).f_sig in

  (* The wp *)
  let pvres = pv_res f in
  let vres = EcIdent.create "result" in
  let fres = f_local vres fsig.fs_ret in
  let post = wp_asgn_call env m lp fres bhs.bhs_po in
  let fpost = PVM.subst1 env pvres m fres fpost in 
  let modi = f_write env f in
  let post = generalize_mod env m modi (f_imp_simpl fpost post) in
  let post = f_forall_simpl [(vres, GTty fsig.fs_ret)] post in
  let spre = subst_args_call env m f fsig.fs_params args PVM.empty in
  let post = f_anda_simpl (PVM.subst env spre fpre) post in

  (* most of the above code is duplicated from t_hoare_call *)
  let f_concl = bdHoare_call_spec fpre fpost f bhs.bhs_cmp bhs.bhs_bd opt_bd in
  let concl = match bhs.bhs_cmp, opt_bd with
    | FHle, None -> f_hoareS bhs.bhs_m bhs.bhs_pr s post 
    | FHeq, Some bd ->
      f_bdHoareS_r 
        { bhs with bhs_s = s; bhs_po=post; bhs_bd=f_real_div bhs.bhs_bd bd} 
    | FHeq, None -> 
      f_bdHoareS_r { bhs with bhs_s = s; bhs_po=post; bhs_bd=f_r1 } 
    | FHge, Some bd -> 
      f_bdHoareS_r 
        { bhs with bhs_s = s; bhs_po=post; bhs_bd=f_real_div bhs.bhs_bd bd} 
    | FHge, None -> 
      f_bdHoareS_r { bhs with bhs_s = s; bhs_po=post; bhs_cmp=FHeq; bhs_bd=f_r1}
    | _, _ -> assert false
  in
  prove_goal_by [f_concl;concl] (RN_hl_call (None, fpre, fpost)) g

      

let t_equiv_call fpre fpost g =
  (* FIXME : check the well formess of the pre and the post ? *)
  let env,_,concl = get_goal_e g in
  let es = destr_equivS concl in
  let (lpl,fl,argsl),(lpr,fr,argsr),sl,sr = 
    s_last_calls "call" es.es_sl es.es_sr in
  let ml = EcMemory.memory es.es_ml in
  let mr = EcMemory.memory es.es_mr in
  let fsigl = (Fun.by_xpath fl env).f_sig in
  let fsigr = (Fun.by_xpath fr env).f_sig in
  (* The functions satisfy their specification *)
  let f_concl = f_equivF fpre fl fr fpost in
  (* The wp *)
  let pvresl = pv_res fl and pvresr = pv_res fr in
  let vresl = LDecl.fresh_id (get_hyps g) "result_L" in
  let vresr = LDecl.fresh_id (get_hyps g) "result_R" in
  let fresl = f_local vresl fsigl.fs_ret in
  let fresr = f_local vresr fsigr.fs_ret in
  let post = wp_asgn_call env ml lpl fresl es.es_po in
  let post = wp_asgn_call env mr lpr fresr post in
  let s    = 
    PVM.add env pvresl ml fresl (PVM.add env pvresr mr fresr PVM.empty) in   
  let fpost = PVM.subst env s fpost in 
  let modil = f_write env fl in
  let modir = f_write env fr in
  let post = generalize_mod env mr modir (f_imp_simpl fpost post) in
  let post = generalize_mod env ml modil post in
  let post = 
    f_forall_simpl
      [(vresl, GTty fsigl.fs_ret);
       (vresr, GTty fsigr.fs_ret)]
      post in
  let spre = subst_args_call env ml fl fsigl.fs_params argsl PVM.empty in
  let spre = subst_args_call env mr fr fsigr.fs_params argsr spre in
  let post = f_anda_simpl (PVM.subst env spre fpre) post in
  let concl = f_equivS_r { es with es_sl = sl; es_sr = sr; es_po=post} in
  prove_goal_by [f_concl;concl] (RN_hl_call (None, fpre, fpost)) g

(* TODO generalize the rule for any lossless statement *)
let t_equiv_call1 side fpre fpost g =
  let env,_,concl = get_goal_e g in
  let equiv = destr_equivS concl in

  let (me, stmt) =
    match side with
    | true  -> (EcMemory.memory equiv.es_ml, equiv.es_sl)
    | false -> (EcMemory.memory equiv.es_mr, equiv.es_sr)
  in

  let (lp, f, args), fstmt = s_last_call "call" stmt in
  let fsig = (Fun.by_xpath f env).f_sig in

  (* The function satisfies its specification *)
  let fconcl = f_bdHoareF fpre f fpost FHeq f_r1 in

  (* WP *)
  let pvres  = pv_res f in
  let vres   = LDecl.fresh_id (get_hyps g) "result" in
  let fres   = f_local vres fsig.fs_ret in
  let post   = wp_asgn_call env me lp fres equiv.es_po in
  let subst  = PVM.add env pvres me fres PVM.empty in
  let msubst = Fsubst.f_bind_mem Fsubst.f_subst_id EcFol.mhr me in
  let fpost  = PVM.subst env subst (Fsubst.f_subst msubst fpost) in
  let modi   = f_write env f in
  let post   = f_imp_simpl fpost post in
  let post   = generalize_mod env me modi post in
  let spre   = PVM.empty in
  let spre   = subst_args_call env me f fsig.fs_params args spre in
  let post   = f_anda_simpl (PVM.subst env spre (Fsubst.f_subst msubst fpre)) post in
  let concl  =
    match side with
    | true  -> { equiv with es_sl = fstmt; es_po = post; }
    | false -> { equiv with es_sr = fstmt; es_po = post; } in
  let concl  = f_equivS_r concl in
  let concl  = f_forall [(vres, GTty fsig.fs_ret)] concl in
  prove_goal_by [fconcl; concl] (RN_hl_call (Some side, fpre, fpost)) g

(* --------------------------------------------------------------------- *)

let t_hoare_equiv p q p1 q1 p2 q2 g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  let s1 = Fsubst.f_bind_mem Fsubst.f_subst_id mhr (fst es.es_ml) in
  let s2 = Fsubst.f_bind_mem Fsubst.f_subst_id mhr (fst es.es_mr) in
  let concl1 = 
    gen_mems [es.es_ml;es.es_mr] 
      (f_imp es.es_pr (f_and p (f_and (Fsubst.f_subst s1 p1) (Fsubst.f_subst s2 p2)))) in
  let concl2 = 
    gen_mems [es.es_ml;es.es_mr]
      (f_imps [q;Fsubst.f_subst s1 q1;Fsubst.f_subst s2 q2] es.es_po) in
  let concl3 = 
    f_hoareS (mhr,snd es.es_ml) p1 es.es_sl q1 in
  let concl4 = 
    f_hoareS (mhr,snd es.es_mr) p2 es.es_sr q2 in
  let concl5 = 
    f_equivS_r { es with es_pr = p; es_po = q } in
  prove_goal_by [concl1; concl2; concl3; concl4; concl5] 
    RN_hl_hoare_equiv g

(*
let t_equiv_mod 
{P} c1 ~ c2 {Q}
P => forall mod, Q => Q' 
-------------------------
{P} c1 ~ c2 {Q'}
*)

(*
let t_equiv_true 
lossless c1
lossless c2
------------------
{P} c1 ~ c2 {true}

*)

(* --------------------------------------------------------------------- *)
let t_hoare_case f g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  let concl1 = f_hoareS_r { hs with hs_pr = f_and_simpl hs.hs_pr f } in
  let concl2 = f_hoareS_r { hs with hs_pr = f_and_simpl hs.hs_pr (f_not f) } in
  prove_goal_by [concl1;concl2] (RN_hl_case f) g

let t_bdHoare_case f g =
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in
  let concl1 = f_bdHoareS_r { bhs with bhs_pr = f_and_simpl bhs.bhs_pr f } in
  let concl2 = f_bdHoareS_r { bhs with bhs_pr = f_and_simpl bhs.bhs_pr (f_not f) } in
  prove_goal_by [concl1;concl2] (RN_hl_case f) g

let t_equiv_case f g = 
  let concl = get_concl g in
  let es = destr_equivS concl in
  let concl1 = f_equivS_r { es with es_pr = f_and es.es_pr f } in
  let concl2 = f_equivS_r { es with es_pr = f_and es.es_pr (f_not f) } in
  prove_goal_by [concl1;concl2] (RN_hl_case f) g

let t_he_case f g =
  t_hS_or_bhS_or_eS (t_hoare_case f) (t_bdHoare_case f) (t_equiv_case f) g 

(* --------------------------------------------------------------------- *)
let _inline_freshen me v =
  let rec for_idx idx =
    let x = Printf.sprintf "%s%d" v.v_name idx in
      if EcMemory.is_bound x me then
        for_idx (idx+1)
      else
        (EcMemory.bind x v.v_type me, x)
  in
    if EcMemory.is_bound v.v_name me then
      for_idx 0
    else
      (EcMemory.bind v.v_name v.v_type me, v.v_name)

let _inline hyps me sp s =
  let env = LDecl.toenv hyps in
  let module P = EcPath in

  let inline1 me lv p args = 
    let p = EcEnv.NormMp.norm_xpath env p in
    let f = EcEnv.Fun.by_xpath p env in
    let fdef = 
      match f.f_def with
      | FBdef def -> def 
      | _ -> assert false in (* FIXME error message *)
    let me, anames = 
      List.map_fold _inline_freshen me f.f_sig.fs_params in
    let me, lnames = 
      List.map_fold _inline_freshen me fdef.f_locals in
    let subst =
      let for1 mx v x =
        (* Remark p is in normal form so (P.xqname p v.v_name) is *)
        P.Mx.add
          (P.xqname p v.v_name)
          (P.xqname (EcMemory.xpath me) x)
          mx
      in
      let mx = P.Mx.empty in
      let mx = List.fold_left2 for1 mx f.f_sig.fs_params anames in
      let mx = List.fold_left2 for1 mx fdef.f_locals lnames in
      let on_xp xp =
        let xp' = EcEnv.NormMp.norm_xpath env xp in
        P.Mx.find_def xp xp' mx 
      in
      { e_subst_id with es_xp = on_xp }
    in

    let prelude =
      List.map2
        (fun (v, newx) e ->
          let newpv = pv_loc (EcMemory.xpath me) newx in
          i_asgn (LvVar (newpv, v.v_type), e))
        (List.combine f.f_sig.fs_params anames)
        args in

    let body  = s_subst subst fdef.f_body in

    let resasgn =
      match fdef.f_ret with
      | None   -> None
      | Some r -> Some (i_asgn (oget lv, e_subst subst r)) in

    me, prelude @ body.s_node @ (otolist resasgn) in

  let rec inline_i me ip i = 
    match ip, i.i_node with
    | IPpat, Scall (lv, p, args) -> 
      inline1 me lv p args 
    | IPif(sp1, sp2), Sif(e,s1,s2) ->
      let me,s1 = inline_s me sp1 s1.s_node in
      let me,s2 = inline_s me sp2 s2.s_node in
      me, [i_if(e,stmt s1, stmt s2)]
    | IPwhile sp, Swhile(e,s) ->
      let me,s = inline_s me sp s.s_node in
      me, [i_while(e,stmt s)]
    | _, _ -> assert false (* FIXME error message *)
  and inline_s me sp s = 
    match sp with
    | [] -> me, s
    | (toskip,ip)::sp ->
      let r,i,s = List.split_n toskip s in
      let me,si = inline_i me ip i in
      let me,s = inline_s me sp s in
      me, List.rev_append r (si @ s) in
  let me, s = inline_s me sp s.s_node in
  me, stmt s 

let t_inline_bdHoare sp g =
  let hyps,concl = get_goal g in
  let hoare      = destr_bdHoareS concl in
  let (me, stmt) = _inline hyps hoare.bhs_m sp hoare.bhs_s in
  let concl      = f_bdHoareS_r { hoare with bhs_m = me; bhs_s = stmt; } in
  prove_goal_by [concl] (RN_hl_inline (None, sp)) g

let t_inline_hoare sp g =
  let hyps,concl = get_goal g in
  let hoare      = destr_hoareS concl in
  let (me, stmt) = _inline hyps hoare.hs_m sp hoare.hs_s in
  let concl      = f_hoareS_r { hoare with hs_m = me; hs_s = stmt; } in
  prove_goal_by [concl] (RN_hl_inline (None, sp)) g

let t_inline_equiv side sp g =
  let hyps,concl = get_goal g in
  let equiv = destr_equivS concl in
  let concl =
    match side with
    | true  ->
      let (me, stmt) = _inline hyps equiv.es_ml sp equiv.es_sl in
      f_equivS_r { equiv with es_ml = me; es_sl = stmt; }
    | false ->
      let (me, stmt) = _inline hyps equiv.es_mr sp equiv.es_sr in
      f_equivS_r { equiv with es_mr = me; es_sr = stmt; }
  in
  prove_goal_by [concl] (RN_hl_inline (Some side, sp)) g

(* -------------------------------------------------------------------- *)
let t_kill side cpos olen g =
  let env = LDecl.toenv (get_hyps g) in
  let kill_stmt _env (_, po) me zpr =
    let error fmt =
      Format.ksprintf
        (fun msg -> tacuerror "cannot kill code, %s" msg)
        fmt
    in

    let (ks, tl) =
      match olen with
      | None -> (zpr.Zpr.z_tail, [])
      | Some len ->
          if List.length zpr.Zpr.z_tail < len then
            tacuerror "cannot find %d consecutive instructions at given position" len;
          List.take_n len zpr.Zpr.z_tail
    in

    let ks_wr = is_write env PV.empty ks in
    (* TODO Benj : check the usage of po_rd *)
    let po_rd = PV.fv env (fst me) po in

    List.iteri
      (fun i is ->
         let is_rd = is_read env PV.empty is in
           if not (PV.indep env ks_wr is_rd) then
             match i with
             | 0 -> error "code writes variables used by the current block"
             | _ -> error "code writes variables used by the %dth parent block" i)
      (Zpr.after ~strict:false { zpr with Zpr.z_tail = tl; });

    if not (PV.indep env ks_wr po_rd) then
      error "code writes variables used by the post-condition";

    let kslconcl = EcFol.f_bdHoareS me f_true (stmt ks) f_true FHeq f_r1 in
      (me, { zpr with Zpr.z_tail = tl; }, [kslconcl])
  in

  let tr = fun side -> RN_hl_kill (side, cpos, olen) in
    t_code_transform side ~bdhoare:true cpos tr (t_zip kill_stmt) g

(* -------------------------------------------------------------------- *)
let alias_stmt id _ me i =
  match i.i_node with
  | Srnd (lv, e) ->
      let id       = odfl "x" (omap id EcLocation.unloc) in
      let ty       = ty_of_lv lv in
      let id       = { v_name = id; v_type = ty; } in
      let (me, id) = _inline_freshen me id in
      let pv       = pv_loc (EcMemory.xpath me) id in

        (me, [i_rnd (LvVar (pv, ty), e); i_asgn (lv, e_var pv ty)])

  | _ ->
      tacuerror "cannot create an alias for that kind of instruction"

let t_alias side cpos id g =
  let tr = fun side -> RN_hl_alias (side, cpos) in
  t_code_transform side cpos tr (t_fold (alias_stmt id)) g

(* -------------------------------------------------------------------- *)
let check_fission_independence env b init c1 c2 c3 =
  (* TODO improve error message, see swap *)
  let check_disjoint s1 s2 = 
    if not (PV.indep env s1 s2) then
      tacuerror "in loop-fission, independence check failed"
  in

  let fv_b    = e_read   env PV.empty b    in
  let rd_init = is_read  env PV.empty init in
  let wr_init = is_write env PV.empty init in
  let rd_c1   = is_read  env PV.empty c1   in
  let rd_c2   = is_read  env PV.empty c2   in
  let rd_c3   = is_read  env PV.empty c3   in
  let wr_c1   = is_write env PV.empty c1   in
  let wr_c2   = is_write env PV.empty c2   in
  let wr_c3   = is_write env PV.empty c3   in

  check_disjoint rd_c1 wr_c2;
  check_disjoint rd_c2 wr_c1;
  List.iter (check_disjoint fv_b) [wr_c1; wr_c2];
  check_disjoint fv_b (PV.diff wr_c3 wr_init);
   List.iter (check_disjoint rd_init) [wr_init; wr_c1; wr_c3];
  List.iter (check_disjoint rd_c3) [wr_c1; wr_c2]

(* -------------------------------------------------------------------- *)
let fission_stmt (il, (d1, d2)) env me zpr =
  if d2 < d1 then
    tacuerror "%s, %s"
      "in loop-fission"
      "second break offset must not be lower than the first one";
  
  let (hd, init, b, sw, tl) =
    match zpr.Zpr.z_tail with
    | { i_node = Swhile (b, sw) } :: tl -> begin
        if List.length zpr.Zpr.z_head < il then
          tacuerror "while-loop is not headed by %d intructions" il;
      let (init, hd) = List.take_n il zpr.Zpr.z_head in
        (hd, init, b, sw, tl)
      end
    | _ -> tacuerror "code position does not lead to a while-loop"
  in

  if d2 > List.length sw.s_node then
    tacuerror "in loop fission, invalid offsets range";

  let (s1, s2, s3) =
    let (s1, s2) = List.take_n (d1   ) sw.s_node in
    let (s2, s3) = List.take_n (d2-d1) s2 in
      (s1, s2, s3)
  in

  check_fission_independence env b init s1 s2 s3;

  let wl1 = i_while (b, stmt (s1 @ s3)) in
  let wl2 = i_while (b, stmt (s2 @ s3)) in
  let fis =   (List.rev_append init [wl1])
            @ (List.rev_append init [wl2]) in

    (me, { zpr with Zpr.z_head = hd; Zpr.z_tail = fis @ tl }, [])

let t_fission side cpos infos g =
  let tr = fun side -> RN_hl_fission (side, cpos, infos) in
  let cb = fun hyps _ me zpr -> fission_stmt infos (LDecl.toenv hyps) me zpr in
    t_code_transform side cpos tr (t_zip cb) g

(* -------------------------------------------------------------------- *)
let fusion_stmt (il, (d1, d2)) env me zpr =
  let (hd, init1, b1, sw1, tl) =
    match zpr.Zpr.z_tail with
    | { i_node = Swhile (b, sw) } :: tl -> begin
        if List.length zpr.Zpr.z_head < il then
          tacuerror "1st while-loop is not headed by %d intruction(s)" il;
      let (init, hd) = List.take_n il zpr.Zpr.z_head in
        (hd, init, b, sw, tl)
      end
    | _ -> tacuerror "code position does not lead to a while-loop"
  in

  let (init2, b2, sw2, tl) =
    if List.length tl < il then
      tacuerror "1st first-loop is not followed by %d instruction(s)" il;
    let (init2, tl) = List.take_n il tl in
      match tl with
      | { i_node = Swhile (b2, sw2) } :: tl -> (List.rev init2, b2, sw2, tl)
      | _ -> tacuerror "cannot find the 2nd while-loop"
  in

  if d1 > List.length sw1.s_node then
    tacuerror "in loop-fusion, body is less than %d instruction(s)" d1;
  if d2 > List.length sw2.s_node then
    tacuerror "in loop-fusion, body is less than %d instruction(s)" d2;

  let (sw1, fini1) = List.take_n d1 sw1.s_node in
  let (sw2, fini2) = List.take_n d2 sw2.s_node in

  (* FIXME: costly *)
  if not (EcReduction.s_equal_norm env (stmt init1) (stmt init2)) then
    tacuerror "in loop-fusion, preludes do not match";
  if not (EcReduction.s_equal_norm env (stmt fini1) (stmt fini2)) then
    tacuerror "in loop-fusion, finalizers do not match";
  if not (EcReduction.e_equal_norm env b1 b2) then
    tacuerror "in loop-fusion, while conditions do not match";

  check_fission_independence env b1 init1 sw1 sw2 fini1;

  let wl  = i_while (b1, stmt (sw1 @ sw2 @ fini1)) in
  let fus = List.rev_append init1 [wl] in

    (me, { zpr with Zpr.z_head = hd; Zpr.z_tail = fus @ tl; }, [])

let t_fusion side cpos infos g =
  let tr = fun side -> RN_hl_fusion (side, cpos, infos) in
  let cb = fun hyps _ me zpr -> fusion_stmt infos (LDecl.toenv hyps) me zpr in
    t_code_transform side cpos tr (t_zip cb) g

(* -------------------------------------------------------------------- *)
let unroll_stmt _ me i =
  match i.i_node with
  | Swhile (e, sw) -> (me, [i_if (e, sw, stmt []); i])
  | _ -> tacuerror "cannot find a while loop at given position"

let t_unroll side cpos g =
  let tr = fun side -> RN_hl_unroll (side, cpos) in
    t_code_transform side cpos tr (t_fold unroll_stmt) g

(* -------------------------------------------------------------------- *)
let splitwhile_stmt b _env me i =
  match i.i_node with
  | Swhile (e, sw) -> 
      let op_and = e_op EcCoreLib.p_and [] (tfun tbool (tfun tbool tbool)) in
      let e = e_app op_and [e; b] tbool in
        (me, [i_while (e, sw); i])

  | _ -> tacuerror "cannot find a while loop at given position"

let t_splitwhile b side cpos g =
  let tr = fun side -> RN_hl_splitwhile (b, side, cpos) in
    t_code_transform side cpos tr (t_fold (splitwhile_stmt b)) g

(* -------------------------------------------------------------------- *)
let cfold_stmt env me olen zpr =

  let (asgn, i, tl) =
    match zpr.Zpr.z_tail with
    | ({ i_node = Sasgn (lv, e) } as i) :: tl -> begin
      let asgn =
        match lv with
        | LvMap _ -> tacuerror "left-value is a map assignment"
        | LvVar (x, ty) -> [(x, ty, e)]
        | LvTuple xs -> begin
          match e.e_node with
          | Etuple es -> List.map2 (fun (x, ty) e -> (x, ty, e)) xs es
          | _ -> assert false
        end
      in
        (asgn, i, tl)
    end

    | _ -> 
        tacuerror "cannot find a left-value assignment at given position"
  in

  let (tl1, tl2) =
    match olen with
    | None      -> (tl, [])
    | Some olen ->
        if List.length tl < olen then
          tacuerror "expecting at least %d instructions after assignment" olen;
        List.take_n olen tl
  in

  List.iter
    (fun (x, _, _) ->
      if x.pv_kind <> PVloc then
        tacuerror "left-values must be local variables")
    asgn;

  List.iter
    (fun (_, _, e) ->
        if e_fv e <> Mid.empty || e_read env PV.empty e <> PV.empty then
          tacuerror "right-values are not closed expression")
    asgn;

  let wrs = is_write env EcPV.PV.empty tl1 in
  let asg = List.fold_left
              (fun pv (x, ty, _) -> EcPV.PV.add env x ty pv)
              EcPV.PV.empty asgn
  in

  if not (EcPV.PV.indep env wrs asg) then
    tacuerror "cannot cfold non read-only local variables";

  let subst =
    List.fold_left
      (fun subst (x, _ty, e) ->
         Mpv.add env x e subst)
      Mpv.empty asgn
  in

  let tl1 = Mpv.issubst env subst tl1 in

  let zpr =
    { zpr with Zpr.z_tail = tl1 @ (i :: tl2) }
  in
    (me, zpr, [])

let t_cfold side cpos olen g =
  let tr = fun side -> RN_hl_cfold (side, cpos, olen) in
  let cb = fun hyps _ me zpr -> cfold_stmt (LDecl.toenv hyps) me olen zpr in 
    t_code_transform ~bdhoare:true side cpos tr (t_zip cb) g

(* -------------------------------------------------------------------- *)
let t_bdHoare_deno pre post g =
  let env,_,concl = get_goal_e g in
  let cmp, f, bd, concl_post =
    match concl.f_node with
    | Fapp({f_node = Fop(op,_)}, [f;bd]) when is_pr f &&
        EcPath.p_equal op EcCoreLib.p_real_le ->
      FHle, f, bd, fun ev -> f_imp_simpl ev post
    | Fapp({f_node = Fop(op,_)}, [f;bd]) when is_pr f &&
        EcPath.p_equal op EcCoreLib.p_eq ->
      FHeq, f, bd, f_iff_simpl post
    | Fapp({f_node = Fop(op,_)}, [bd;f]) when is_pr f &&
        (EcPath.p_equal op EcCoreLib.p_eq) ->
      FHeq, f, bd, f_iff_simpl post
    | Fapp({f_node = Fop(op,_)}, [bd;f]) when is_pr f &&
        EcPath.p_equal op EcCoreLib.p_real_le ->
      FHge, f, bd, f_imp_simpl post
    | _ -> cannot_apply "hoare_deno" "" (* FIXME error message *)
  in 
  let (m,f,args,ev) = destr_pr f in
  let concl_e = f_bdHoareF pre f post cmp bd in
  let fun_ = EcEnv.Fun.by_xpath f env in
  (* building the substitution for the pre *)
  let sargs = 
    List.fold_left2 (fun s v a -> PVM.add env (pv_loc f v.v_name) mhr a s)
      PVM.empty fun_.f_sig.fs_params args in
  let smem = Fsubst.f_bind_mem Fsubst.f_subst_id mhr m in
  let concl_pr  = Fsubst.f_subst smem (PVM.subst env sargs pre) in
  (* building the substitution for the post *)
  (* FIXME: *)
  (* let smem_ = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mhr in  *)
  (* let ev   = Fsubst.f_subst smem_ ev in *)
  let me = EcEnv.Fun.actmem_post mhr f fun_ in
  let concl_po = gen_mems [me] (concl_post ev) in
  prove_goal_by [concl_e;concl_pr;concl_po] RN_hl_deno g  


let t_equiv_deno pre post g =
  let env, _, concl = get_goal_e g in
  let cmp, f1, f2 =
    match concl.f_node with
    | Fapp({f_node = Fop(op,_)}, [f1;f2]) when is_pr f1 && is_pr f2 &&
        (EcPath.p_equal op EcCoreLib.p_eq || 
           EcPath.p_equal op EcCoreLib.p_real_le) ->
      EcPath.p_equal op EcCoreLib.p_eq, f1, f2
    | _ -> cannot_apply "equiv_deno" "" in (* FIXME error message *)
  let (ml,fl,argsl,evl) = destr_pr f1 in
  let (mr,fr,argsr,evr) = destr_pr f2 in
  let concl_e = f_equivF pre fl fr post in
  let funl = EcEnv.Fun.by_xpath fl env in
  let funr = EcEnv.Fun.by_xpath fr env in
  (* building the substitution for the pre *)
  (* we should substitute param by args and left by ml and right by mr *)
  let sargs = 
    List.fold_left2 (fun s v a -> PVM.add env (pv_loc fr v.v_name) mright a s)
      PVM.empty funr.f_sig.fs_params argsr in
  let sargs = 
    List.fold_left2 (fun s v a -> PVM.add env (pv_loc fl v.v_name) mleft a s)
      sargs funl.f_sig.fs_params argsl in
  let smem = 
    Fsubst.f_bind_mem (Fsubst.f_bind_mem Fsubst.f_subst_id mright mr) mleft ml in
  let concl_pr  = Fsubst.f_subst smem (PVM.subst env sargs pre) in
  (* building the substitution for the post *)
  let smeml = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mleft in 
  let smemr = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mright in
  let evl   = Fsubst.f_subst smeml evl and evr = Fsubst.f_subst smemr evr in
  let cmp   = if cmp then f_iff else f_imp in 
  let mel = EcEnv.Fun.actmem_post mleft fl funl in
  let mer = EcEnv.Fun.actmem_post mright fr funr in
  let concl_po = gen_mems [mel;mer] (f_imp post (cmp evl evr)) in
  prove_goal_by [concl_e;concl_pr;concl_po] RN_hl_deno g  


(* -------------------------------------------------------------------- *)

let gen_rcond b m at_pos s =
  let head, i, tail = s_split_i "rcond" at_pos s in 
  let e, s = 
    match i.i_node with
    | Sif(e,s1,s2) -> e, if b then s1.s_node else s2.s_node
    | Swhile(e,s1) -> e, if b then s1.s_node@[i] else [] 
    | _ -> 
      cannot_apply "rcond" 
        (Format.sprintf "the %ith instruction is not a conditionnal" at_pos) in
  let e = form_of_expr m e in
  let e = if b then e else f_not e in
  stmt head, e, stmt (head@s@tail)
  
let t_hoare_rcond b at_pos g = 
  (* TODO: generalize the rule using assume *)
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  let m  = EcMemory.memory hs.hs_m in 
  let hd,e,s = gen_rcond b m at_pos hs.hs_s in
  let concl1  = f_hoareS_r { hs with hs_s = hd; hs_po = e } in
  let concl2  = f_hoareS_r { hs with hs_s = s } in
  prove_goal_by [concl1;concl2] (RN_hl_rcond (None, b,at_pos)) g  

let t_bdHoare_rcond b at_pos g = 
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in
  let m  = EcMemory.memory bhs.bhs_m in 
  let hd,e,s = gen_rcond b m at_pos bhs.bhs_s in
  let concl1  = f_hoareS bhs.bhs_m bhs.bhs_pr hd e in
  let concl2  = f_bdHoareS_r { bhs with bhs_s = s } in
  prove_goal_by [concl1;concl2] (RN_hl_rcond (None, b,at_pos)) g  

let t_equiv_rcond side b at_pos g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  let m,mo,s = 
    if side then es.es_ml,es.es_mr, es.es_sl 
    else         es.es_mr,es.es_ml, es.es_sr in
  let hd,e,s = gen_rcond b EcFol.mhr at_pos s in 
  let mo' = EcIdent.create "&m" in
  let s1 = 
    Fsubst.f_bind_mem 
      (Fsubst.f_bind_mem Fsubst.f_subst_id (EcMemory.memory m) EcFol.mhr)
      (EcMemory.memory mo) mo' in
  let pre1  = Fsubst.f_subst s1 es.es_pr in
  let concl1 = 
    gen_mems [mo', EcMemory.memtype mo] 
      (f_hoareS (EcFol.mhr,EcMemory.memtype m) pre1 hd e) in
  let sl,sr = if side then s, es.es_sr else es.es_sl, s in
  let concl2 = f_equivS_r { es with es_sl = sl; es_sr = sr } in
  prove_goal_by [concl1;concl2] (RN_hl_rcond (Some side,b,at_pos)) g 

let t_rcond side b at_pos g =
  let concl = get_concl g in
  match side with
    | None when is_bdHoareS concl -> t_bdHoare_rcond b at_pos g
    | None -> t_hoare_rcond b at_pos g
    | Some side -> t_equiv_rcond side b at_pos g

(* -------------------------------------------------------------------- *)

(* FAILURE EVENT LEMMA  *)

(* in EcPath.mli: *)



(* takes an xpath, returns xpath set *)
let callable_oracles_f env os f =
  let f = NormMp.norm_xpath env f in
  let func = Fun.by_xpath f env in
  match func.f_def with
    | FBabs oi ->
      List.fold_left (fun s o -> EcPath.Sx.add o s) os oi.oi_calls
  | FBdef fdef ->
    List.fold_left (fun s o -> EcPath.Sx.add o s) 
      os fdef.f_uses.us_calls

let rec callable_oracles_s env os s =
  callable_oracles_is env os s.s_node
and callable_oracles_is env os is = 
  List.fold_left (callable_oracles_i env) os is
and callable_oracles_i env os i = 
  match i.i_node with
    | Scall(_,f,_) -> callable_oracles_f env os f
    | Sif (_,s1,s2) -> callable_oracles_s env (callable_oracles_s env os s1) s2
    | Swhile (_,s) -> callable_oracles_s env os s
    | Sasgn _ | Srnd _ | Sassert _ -> os 

let callable_oracles_stmt env = callable_oracles_s env EcPath.Sx.empty

let t_failure_event at_pos cntr delta q f_event some_p g =
  let env,_,concl = get_goal_e g in
  match concl.f_node with
    | Fapp ({f_node=Fop(op,_)},[pr;bd]) when is_pr pr 
        && EcPath.p_equal op EcCoreLib.p_real_le ->
      let (m,f,_args,ev) = destr_pr pr in
      let m = match Memory.byid m env with 
        | Some m -> m 
        | None -> cannot_apply "fel" "Cannot find memory (bug?)"
      in
      let memenv, fdef, _env = 
        try Fun.hoareS f env
        with _ -> 
          cannot_apply "fel" "not applicable to abstract functions"
      in
      let s_hd,s_tl = s_split "fel" at_pos fdef.f_body in
      let os = callable_oracles_stmt env (stmt s_tl) in
      (* check that bad event is only modified in oracles *)
      let fv = PV.fv env mhr f_event in
      if not (PV.indep env (s_write ~except_fs:os env (stmt s_tl)) (fv) ) then
        cannot_apply "fel" "fail event is modified outside oracles";
      (* subgoal on the bounds *)
      let bound_goal = 
        let v1 = f_real_of_int (f_int_prod q (f_int_sub q (f_int 1))) in
        let v = f_real_prod v1 delta  in
        f_real_le v bd
      in
      (* we must quantify over memories *)
      let mo = EcIdent.create "&m" in
      let post_goal = 
        let subst = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mo in
        let p = f_imp ev (f_and f_event (f_int_le cntr q)) in
        let p = Fsubst.f_subst subst p in
        gen_mems [mo, EcMemory.memtype m] p 
      in
      (* not fail and cntr=0 holds at designated program point *)
      let init_goal = 
        let p = f_and (f_not f_event) (f_eq cntr (f_int 0)) in
        f_hoareS memenv f_true (stmt s_hd) p
      in
      let oracle_goal o = 
        let not_F_to_F_goal = 
          let bound = f_real_prod (f_real_of_int cntr) delta in
          let pre = f_not f_event in
          let post = f_event in
          f_bdHoareF pre o post FHle bound
        in
        let old_cntr_id = EcIdent.create "c" in
        let old_b_id = EcIdent.create "b" in
        let old_cntr = f_local old_cntr_id tint in
        let old_b = f_local old_b_id tbool in
        let cntr_decr_goal = 
          let pre  = f_and some_p (f_eq old_cntr cntr) in
          let post = f_int_lt old_cntr cntr in
          f_forall_simpl [old_cntr_id,GTty tint] 
            (f_hoareF pre o post)
        in
        let cntr_stable_goal =
          let pre  = f_ands [f_not some_p;f_eq f_event old_b;f_eq cntr old_cntr] in
          let post = f_ands [f_eq f_event old_b;f_eq cntr old_cntr] in
          f_forall_simpl [old_b_id,GTty tbool; old_cntr_id,GTty tint] 
            (f_hoareF pre o post)
        in
        [not_F_to_F_goal;cntr_decr_goal;cntr_stable_goal]
      in
      let os_goals = List.concat (List.map oracle_goal (Sx.elements os)) in
      prove_goal_by ([bound_goal;post_goal;init_goal]@os_goals) 
        (RN_hl_fel (cntr,delta,q,f_event,some_p) )  g
    | _ -> 
      cannot_apply "failure event lemma" 
        "A goal of the form Pr[ _ ] <= _ was expected"





(* -------------------------------------------------------------------- *)
let check_swap env s1 s2 = 
  let m1,m2 = s_write env s1, s_write env s2 in
  let r1,r2 = s_read env s1, s_read env s2 in
  (* FIXME it is not suffisant *)
  let m2r1 = PV.interdep env m2 r1 in
  let m1m2 = PV.interdep env m1 m2 in
  let m1r2 = PV.interdep env m1 r2 in
  let error s1 s2 d = 
    EcLogic.tacuerror 
      "cannot swap : the two statement are not independants, the first statement can %s %a which can be %s by the second"
      s1 (PV.pp env) d s2 in
  if not (PV.is_empty m2r1) then error "read" "written" m2r1;
  if not (PV.is_empty m1m2) then error "write" "written" m1m2;
  if not (PV.is_empty m1r2) then error "write" "read" m1r2


let swap_stmt env p1 p2 p3 s = 
  let s = s.s_node in
  let len = List.length s in
  if not (1<= p1 && p1 < p2 && p2 <= p3 && p3 <= len) then
    cannot_apply "swap" 
      (Format.sprintf "invalid position, 1 <= %i < %i <= %i <= %i"
         p1 p2 p3 len);
  let hd,tl = List.take_n (p1-1) s in
  let s12,tl = List.take_n (p2-p1) tl in
  let s23,tl = List.take_n (p3-p2+1) tl in
  check_swap env (stmt s12) (stmt s23);
  stmt (List.flatten [hd;s23;s12;tl]) 

let t_hoare_swap p1 p2 p3 g =
  let env,_,concl = get_goal_e g in
  let hs    = destr_hoareS concl in
  let s = swap_stmt env p1 p2 p3 hs.hs_s in
  let concl = f_hoareS_r {hs with hs_s = s } in
  prove_goal_by [concl] (RN_hl_swap(None,p1,p2,p3)) g

let t_bdHoare_swap p1 p2 p3 g =
  let env,_,concl = get_goal_e g in
  let bhs    = destr_bdHoareS concl in
  let s = swap_stmt env p1 p2 p3 bhs.bhs_s in
  let concl = f_bdHoareS_r {bhs with bhs_s = s } in
  prove_goal_by [concl] (RN_hl_swap(None,p1,p2,p3)) g

let t_equiv_swap side p1 p2 p3 g =
  let env,_,concl = get_goal_e g in
  let es    = destr_equivS concl in
  let sl,sr = 
    if side 
    then swap_stmt env p1 p2 p3 es.es_sl, es.es_sr 
    else es.es_sl, swap_stmt env p1 p2 p3 es.es_sr 
  in
  let concl = f_equivS_r {es with es_sl = sl; es_sr = sr } in
  prove_goal_by [concl] (RN_hl_swap(Some side,p1,p2,p3)) g
    
(* -------------------------------------------------------------------- *)

let s_first_if s = 
  match s.s_node with
  | [] -> cannot_apply "if" "the first instruction should be a if"
  | i::_ -> 
    try destr_if i with Not_found -> 
      cannot_apply "if" "the first instruction should be a if"

let t_gen_cond side e g =
  let hyps = get_hyps g in
  let m1,m2,h,h1,h2 = match LDecl.fresh_ids hyps ["&m";"&m";"_";"_";"_"] with
    | [m1;m2;h;h1;h2] -> m1,m2,h,h1,h2
    | _ -> assert false in
  let t_introm = 
    if side <> None then t_intros_i [m1] else t_id None 
  in
  let t_sub b g = 
    t_seq_subgoal (t_rcond side b 1)
      [t_lseq [t_introm; t_skip; t_intros_i [m2;h];
               t_or  
                 (t_lseq [t_elim_hyp h; t_intros_i [h1;h2]; t_hyp h2])
                 (t_hyp h)
              ];
       t_id None] g in
  t_seq_subgoal (t_he_case e) [t_sub true; t_sub false] g

let t_hoare_cond g = 
  let concl = get_concl g in
  let hs = destr_hoareS concl in 
  let (e,_,_) = s_first_if hs.hs_s in
  t_gen_cond None (form_of_expr (EcMemory.memory hs.hs_m) e) g

let t_bdHoare_cond g = 
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in 
  let (e,_,_) = s_first_if bhs.bhs_s in
  t_gen_cond None (form_of_expr (EcMemory.memory bhs.bhs_m) e) g

let rec t_equiv_cond side g =
  let hyps,concl = get_goal g in
  let es = destr_equivS concl in
  match side with
  | Some s ->
    let e = 
      if s then 
        let (e,_,_) = s_first_if es.es_sl in
        form_of_expr (EcMemory.memory es.es_ml) e
      else
        let (e,_,_) = s_first_if es.es_sr in
        form_of_expr (EcMemory.memory es.es_mr) e in
    t_gen_cond side e g
  | None -> 
      let el,_,_ = s_first_if es.es_sl in
      let er,_,_ = s_first_if es.es_sr in
      let el = form_of_expr (EcMemory.memory es.es_ml) el in
      let er = form_of_expr (EcMemory.memory es.es_mr) er in
      let fiff = gen_mems [es.es_ml;es.es_mr] (f_imp es.es_pr (f_iff el er)) in
      let hiff,m1,m2,h,h1,h2 = 
        match LDecl.fresh_ids hyps ["hiff";"&m1";"&m2";"h";"h";"h"] with 
        | [hiff;m1;m2;h;h1;h2] -> hiff,m1,m2,h,h1,h2 
        | _ -> assert false in
      let t_aux = 
        t_lseq [t_intros_i [m1];
                t_skip;
                t_intros_i [m2;h];
                t_elim_hyp h;
                t_intros_i [h1;h2];
                t_seq_subgoal (t_rewrite_hyp `RtoL hiff 
                                 [AAmem m1;AAmem m2;AAnode])
                  [t_hyp h1; t_hyp h2]] in
      t_seq_subgoal (t_cut fiff)
        [ t_id None;
          t_seq (t_intros_i [hiff])
            (t_seq_subgoal (t_equiv_cond (Some true))
               [t_seq_subgoal (t_equiv_rcond false true  1) 
                   [t_aux; t_clear (Sid.singleton hiff)];
                t_seq_subgoal (t_equiv_rcond false false 1) 
                  [t_aux; t_clear (Sid.singleton hiff)]
               ])
        ] g

(* -------------------------------------------------------------------- *)
let (===) = f_eq 
let (==>) = f_imp
let (&&&) = f_anda

let t_hoare_rnd g =
  let env,_,concl = get_goal_e g in
  let hs = destr_hoareS concl in
  let (lv,distr),s= s_last_rnd "rnd" hs.hs_s in
  (* FIXME: exception when not rnds found *)
  let ty_distr = proj_distr_ty (e_ty distr) in
  let x_id = EcIdent.create (symbol_of_lv lv) in
  let x = f_local x_id ty_distr in
  let distr = EcFol.form_of_expr (EcMemory.memory hs.hs_m) distr in
  let post = subst_form_lv env (EcMemory.memory hs.hs_m) lv x hs.hs_po in
  let post = (f_in_supp x distr) ==> post in
  let post = f_forall_simpl [(x_id,GTty ty_distr)] post in
  let concl = f_hoareS_r {hs with hs_s=s; hs_po=post} in
  prove_goal_by [concl] RN_hl_hoare_rnd g

let wp_equiv_disj_rnd side g =
  let env,_,concl = get_goal_e g in
  let es = destr_equivS concl in
  let m,s = 
    if side then es.es_ml, es.es_sl 
    else         es.es_mr, es.es_sr 
  in
  let (lv,distr),s= s_last_rnd "rnd" s in

  (* FIXME: exception when not rnds found *)
  let ty_distr = proj_distr_ty (e_ty distr) in
  let x_id = EcIdent.create (symbol_of_lv lv) in
  let x = f_local x_id ty_distr in
  let distr = EcFol.form_of_expr (EcMemory.memory m) distr in
  let post = subst_form_lv env (EcMemory.memory m) lv x es.es_po in
  let post = (f_in_supp x distr) ==> post in
  let post = f_forall_simpl [(x_id,GTty ty_distr)] post in
  let concl = 
    if side then f_equivS_r {es with es_sl=s; es_po=post} 
    else  f_equivS_r {es with es_sr=s; es_po=post} 
  in
  prove_goal_by [concl] RN_hl_hoare_rnd g

let wp_equiv_rnd (f,finv) g =
  let env,_,concl = get_goal_e g in
  let es = destr_equivS concl in
  let (lvL,muL),(lvR,muR),sl',sr'= s_last_rnds "rnd" es.es_sl es.es_sr in
  (* FIXME: exception when not rnds found *)
  let tyL = proj_distr_ty (e_ty muL) in
  let tyR = proj_distr_ty (e_ty muR) in
  let x_id = EcIdent.create (symbol_of_lv lvL ^ "L")
  and y_id = EcIdent.create (symbol_of_lv lvR ^ "R") in
  let x = f_local x_id tyL in
  let y = f_local y_id tyR in
  let muL = EcFol.form_of_expr (EcMemory.memory es.es_ml) muL in
  let muR = EcFol.form_of_expr (EcMemory.memory es.es_mr) muR in
  (* *)
  let tf = f tyL tyR in
  let tfinv = finv tyR tyL in
  let f t = f_app tf  [t] tyR in
  let finv t = f_app tfinv [t] tyL in
  let supp_cond1 = (f_in_supp x muL) ==> 
    ((f_mu_x muL x) === (f_mu_x muR (f x))) in
  let supp_cond2 = (f_in_supp y muR) ==> (f_in_supp (finv y) muL) in
  let inv_cond1 =  (f_in_supp x muL) ==> ((finv (f x)) === x) in
  let inv_cond2 =  (f_in_supp y muR) ==> ((f (finv y)) === y) in
  let post = subst_form_lv env (EcMemory.memory es.es_ml) lvL x es.es_po in
  let post = subst_form_lv env (EcMemory.memory es.es_mr) lvR (f x) post in
  let post = (f_in_supp x muL) ==> post in
  let post = supp_cond1 &&& supp_cond2 &&& inv_cond1 &&& inv_cond2 &&& post in
  let post = f_forall_simpl [(x_id,GTty tyL);(y_id,GTty tyR)] post in
  let concl = f_equivS_r {es with es_sl=sl'; es_sr=sr'; es_po=post} in
  prove_goal_by [concl] (RN_hl_equiv_rnd ((Some tf, Some tfinv))) g

let t_equiv_rnd side bij_info =
  match side with
  | Some side -> wp_equiv_disj_rnd side
  | None  ->
    let f,finv =  match bij_info with 
      | Some f, Some finv ->  f, finv
      | Some bij, None | None, Some bij -> bij, bij
      | None, None -> 
        let z_id = EcIdent.create "z" in
        let z = f_local z_id in
        let bij = fun tyL tyR -> f_lambda [z_id,GTty tyR] (z tyL) in 
          (* TODO Cezar : Can it be not well typed: normally tyL and tyR should
             be equal.
             I propose to replace tyL by tyR
          *)
        bij, bij
    in wp_equiv_rnd (f, finv) 

let t_bd_hoare_rnd (opt_bd,opt_event) g =
  let env,_,concl = get_goal_e g in
  let bhs = destr_bdHoareS concl in
  let (lv,distr),s = s_last_rnd "bd_hoare_rnd" bhs.bhs_s in
  let ty_distr = proj_distr_ty (e_ty distr) in
  let distr = EcFol.form_of_expr (EcMemory.memory bhs.bhs_m) distr in
  let event = match opt_event ty_distr with 
    | Some event -> event 
    | None -> cannot_apply "rnd" "Optional events still not supported"
  in

  let v_id = EcIdent.create "v" in
  let v = f_local v_id ty_distr in
  let post_v = subst_form_lv env (EcMemory.memory bhs.bhs_m) lv v bhs.bhs_po in
  let event_v = f_app event [v] tbool in
  let v_in_supp = f_in_supp v distr in

  let concl = 
    match bhs.bhs_cmp, opt_bd with
      | FHle, Some bd' when not (EcFol.f_equal bhs.bhs_bd bd') ->
        cannot_apply "bd_hoare_rnd"
          "Rule for upper-bounded hoare triples requires a total bound"
      | FHle, _ ->
        let bounded_distr = f_real_le (f_mu distr event) bhs.bhs_bd in
        let post_equiv_event = f_forall_simpl [v_id,GTty ty_distr] 
          (f_imps_simpl [v_in_supp;post_v] event_v) in
        let post = bounded_distr &&& post_equiv_event in
        f_hoareS bhs.bhs_m bhs.bhs_pr s post 

      | FHge, Some bd' when not (EcFol.f_equal bhs.bhs_bd bd') -> 
        let new_hoare_bd, bounded_distr =
          EcFol.f_real_div_simpl bhs.bhs_bd bd', f_real_le bd' (f_mu distr event)
        in
        let post_equiv_event = f_forall_simpl [v_id,GTty ty_distr] 
          (f_imps_simpl [v_in_supp;event_v] post_v) in
        let post = bounded_distr &&& post_equiv_event in
        f_bdHoareS_r {bhs with bhs_s=s; bhs_po=post; bhs_bd=new_hoare_bd}

      | FHge, _ -> 
        let bounded_distr = f_real_le bhs.bhs_bd (f_mu distr event) in
        let post_equiv_event = f_forall_simpl [v_id,GTty ty_distr] 
          (f_imps_simpl [v_in_supp;event_v] post_v) in
        let post = bounded_distr &&& post_equiv_event in
        f_bdHoareS_r {bhs with bhs_s=s; bhs_po=post; bhs_cmp=FHeq; bhs_bd=EcFol.f_r1} 

      | FHeq, Some bd' when not (EcFol.f_equal bhs.bhs_bd bd') -> 
        let new_hoare_bd, bounded_distr =
          EcFol.f_real_div_simpl bhs.bhs_bd bd', f_eq (f_mu distr event) bd'
        in
        let post_equiv_event = f_forall_simpl [v_id,GTty ty_distr] 
          (f_imp_simpl v_in_supp (f_iff_simpl event_v post_v)) in
        let post = bounded_distr &&& post_equiv_event in
        f_bdHoareS_r {bhs with bhs_s=s; bhs_po=post; bhs_bd=new_hoare_bd} 

      | FHeq, _ -> 
        let bounded_distr = f_eq (f_mu distr event) bhs.bhs_bd in
        let post_equiv_event = f_forall_simpl [v_id,GTty ty_distr] 
          (f_imp_simpl v_in_supp (f_iff_simpl event_v post_v)) in
        let post = bounded_distr &&& post_equiv_event in
        f_bdHoareS_r {bhs with bhs_s=s; bhs_po=post; bhs_bd=EcFol.f_r1} 
  in
  prove_goal_by [concl] (RN_bhl_rnd (opt_bd,event) ) g



let t_ppr phi_l phi_r g =
  let env,_,concl = get_goal_e g in
  let ef = destr_equivF concl in
  let fl,fr = ef.ef_fl,ef.ef_fr in

  let funl = EcEnv.Fun.by_xpath fl env in
  let funr = EcEnv.Fun.by_xpath fr env in
  let paramsl = funl.f_sig.fs_params in
  let paramsr = funr.f_sig.fs_params in
  let mk_local v =
    let v_id = EcIdent.create v.v_name in
    (v_id,v.v_type),f_local v_id v.v_type
  in
  let argsl = List.map mk_local paramsl in
  let argsr = List.map mk_local paramsr in


  let m1_id = EcIdent.create "&m1" in
  let m2_id = EcIdent.create "&m2" in

  (* let m1 = EcEnv.Fun.prF_memenv m1_id fl env in *)
  (* let m2 = EcEnv.Fun.prF_memenv m2_id fr env in *)
  (* memories must be abstract??!! *)
  let m1 = m1_id,None in
  let m2 = m2_id,None in

  let smem1 = Fsubst.f_bind_mem Fsubst.f_subst_id mleft mhr in
  let smem2 = Fsubst.f_bind_mem Fsubst.f_subst_id mright mhr in
  let phi1 = Fsubst.f_subst smem1 phi_l in
  let phi2 = Fsubst.f_subst smem2 phi_r in
  let pr1 = f_pr m1_id fl (List.map snd argsl) phi1 in
  let pr2 = f_pr m2_id fr (List.map snd argsr) phi2 in

  let concl_pr = f_eq pr1 pr2 in
  let smem = 
    Fsubst.f_bind_mem (Fsubst.f_bind_mem Fsubst.f_subst_id mright m2_id) mleft m1_id
  in
  let pre = Fsubst.f_subst smem ef.ef_pr in
  let concl = gen_mems [m1_id, EcMemory.memtype m1;m2_id,EcMemory.memtype m2] 
    (f_imp pre concl_pr) in
  let binders_l = List.map (fun ((v,t),_) -> v,GTty t ) argsl in
  let binders_r = List.map (fun ((v,t),_) -> v,GTty t ) argsr in
  let concl = f_forall_simpl binders_l (f_forall_simpl binders_r concl) in
  let concl_post = f_imps_simpl [phi_l;phi_r] ef.ef_po in
  prove_goal_by [concl_post;concl] RN_hl_deno g


let t_hoare_bd_hoare g =
  let concl = get_concl g in
  if is_bdHoareS concl then
    let bhs = destr_bdHoareS concl in
    let concl1 = f_hoareS bhs.bhs_m bhs.bhs_pr bhs.bhs_s (f_not bhs.bhs_po) in
    let concl2 = f_eq bhs.bhs_bd f_r0  in
    prove_goal_by [concl1;concl2] RN_hl_hoare_bd_hoare g
  else if is_hoareS concl then
    let hs = destr_hoareS concl in
    let concl1 = f_bdHoareS hs.hs_m hs.hs_pr hs.hs_s (f_not hs.hs_po) FHeq f_r0 in
    prove_goal_by [concl1] RN_hl_hoare_bd_hoare g
  else 
    cannot_apply "hoare/bd_hoare" "a hoare or bd_hoare judgment was expected" 

let t_prbounded g = 
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in 
  let cond = match bhs.bhs_cmp with
    | FHle -> f_real_le f_r1 bhs.bhs_bd
    | FHge -> f_real_le bhs.bhs_bd f_r0
    | FHeq ->
      cannot_apply "pr_bounded" "cannot solve the probabilistic judgement" 
  in
  prove_goal_by [cond] RN_hl_prbounded g

let t_prfalse g = 
  let env,_, concl = get_goal_e g in
  let f,ev,bd =
    match concl.f_node with
      | Fapp ({f_node = Fop(op,_)}, [f;bd]) when is_pr f &&
          EcPath.p_equal op EcCoreLib.p_real_le
          || EcPath.p_equal op EcCoreLib.p_eq->
        let (_m,f,_args,ev) = destr_pr f in
        f,ev,bd
      | Fapp ({f_node = Fop(op,_)}, [bd;f]) when is_pr f &&
          EcPath.p_equal op EcCoreLib.p_eq->
        let (_m,f,_args,ev) = destr_pr f in
        f,ev,bd
      | _ ->
        cannot_apply "pr_false" "Pr[..] expression was expected"
  in
  (* the bound is zero *)
  let is_zero = f_real_le bd f_r0 in

  (* the event is false *)
  let smem_ = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mhr in 
  let ev   = Fsubst.f_subst smem_ ev in
  let fun_ = EcEnv.Fun.by_xpath f env in
  let me = EcEnv.Fun.actmem_post mhr f fun_ in
  let concl_po = gen_mems [me] (f_imp f_false ev) in
  prove_goal_by [is_zero;concl_po] RN_hl_prfalse g

let t_pror g = 
  let concl = get_concl g in
  match concl.f_node with
    | Fapp({f_node=Fop(op1,_)},[{f_node=Fpr(m,f,ps,{f_node=Fapp({f_node=Fop(op2,_)},[p1;p2])})};bd])
        when EcPath.p_equal op1 EcCoreLib.p_eq
          && EcPath.p_equal op2 EcCoreLib.p_or
      ->
      let pr1 = f_pr m f ps p1 in
      let pr2 = f_pr m f ps p2 in
      let pr12 = f_pr m f ps (f_and p1 p2) in
      let pr = f_real_sum pr1 pr2 in
      let pr = f_real_sub pr pr12 in
      let concl = f_eq pr bd in
      prove_goal_by [concl] RN_hl_pror g
    | _ -> 
      cannot_apply "pr_op" "Pr[_ @ _ : _ \\/ _ ] expression was expected"

let t_bdeq g = 
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in 
  let concl = f_bdHoareS_r {bhs with bhs_cmp=FHeq } in
  prove_goal_by [concl] RN_hl_prbounded g
    
(* -------------------------------------------------------------------- *)

(* Remark for adversary case we assume that inv do not contain the
   equality of glob *)
let mk_inv_spec env inv fl fr = 
  if NormMp.is_abstract_fun fl env then 
    let topl,_,oil,sigl, topr, _, _,sigr = abstract_info2 env fl fr in
    let ml, mr = mleft, mright in
    let eqglob = f_eqglob topl ml topr mr in
    let lpre = if oil.oi_in then [eqglob;inv] else [inv] in
    let eq_params = 
      f_eqparams fl sigl.fs_params ml fr sigr.fs_params mr in
    let eq_res = f_eqres fl sigl.fs_ret ml fr sigr.fs_ret mr in
    let pre = f_ands (eq_params::lpre) in
    let post = f_ands [eq_res; eqglob; inv] in
    f_equivF pre fl fr post
  else
    let defl = EcEnv.Fun.by_xpath fl env in
    let defr = EcEnv.Fun.by_xpath fr env in
    let sigl, sigr = defl.f_sig, defr.f_sig in
    let testty = 
      List.all2 (fun v1 v2 -> EcReduction.equal_type env v1.v_type v2.v_type)
        sigl.fs_params sigr.fs_params && 
        EcReduction.equal_type env sigl.fs_ret sigr.fs_ret 
    in
    if not testty then 
      cannot_apply "call" 
        "the two functions should have the same signature";
    let ml, mr = EcFol.mleft, EcFol.mright in
    let eq_params = 
      f_eqparams fl sigl.fs_params ml fr sigr.fs_params mr in
    let eq_res = f_eqres fl sigl.fs_ret ml fr sigr.fs_ret mr in
    let pre = f_and eq_params inv in
    let post = f_and eq_res inv in
    f_equivF pre fl fr post
   
let t_eqobs_inS finfo eqo inv g =
  let env, hyps, concl = get_goal_e g in
  let es = destr_equivS concl in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  (* TODO check that inv contains only global *)
  let ifvl = PV.fv env ml inv in
  let ifvr = PV.fv env mr inv in
  let sl,sr,sg,eqi = 
    EcPV.eqobs_in env finfo 
      es.es_sl es.es_sr eqo (inv,ifvl, ifvr) in
  Format.printf "got %n subgoals@." (List.length sg);
  let post = Mpv2.to_form ml mr eqo inv in
  if not (EcReduction.is_alpha_eq hyps post es.es_po) then
    tacuerror "eqobs_in can not be apply";
  let pre = Mpv2.to_form ml mr eqi inv in
  let concl = 
    f_equivS es.es_ml es.es_mr es.es_pr sl sr pre in
  prove_goal_by (sg@[concl]) RN_eqobs_in g

let rec eqobs_inF eqg env (inv,_,_ as inve) fl fr eqo =
  let nfl = NormMp.norm_xpath env fl in
  let nfr = NormMp.norm_xpath env fl in
  let defl = Fun.by_xpath nfl env in
  let defr = Fun.by_xpath nfr env in
  match defl.f_def, defr.f_def with
  | FBabs oi, FBabs _ -> 
    if not (Mpv2.subset eqo eqg) then raise EqObsInError;
    let top = EcPath.m_functor nfl.EcPath.x_top in
    let ieqg = Mpv2.remove_glob top eqg in
    let peqg = if oi.oi_in then eqg else ieqg in
    let inv = Mpv2.to_form mleft mright ieqg inv in
    peqg, mk_inv_spec env inv fl fr
  | FBdef funl, FBdef funr -> 
    begin 
      try
        let sigl, sigr = defl.f_sig, defr.f_sig in
        let testty = 
          List.all2 (fun v1 v2 -> 
            EcReduction.equal_type env v1.v_type v2.v_type)
            sigl.fs_params sigr.fs_params && 
            EcReduction.equal_type env sigl.fs_ret sigr.fs_ret 
        in
        if not testty then raise EqObsInError;
        let eqo = 
          match funl.f_ret, funr.f_ret with
          | None, None -> eqo
          | Some el, Some er -> add_eqs env eqo el er 
          | _, _ -> raise EqObsInError in
        let sl, sr, _, eqi = 
          eqobs_in env (eqobs_inF eqg) funl.f_body funr.f_body eqo inve in
        if sl.s_node <> [] || sr.s_node <> [] then raise EqObsInError;
        let geqi = 
          List.fold_left2 (fun eqi vl vr ->
            Mpv2.remove env (pv_loc nfl vl.v_name) (pv_loc nfr vr.v_name) eqi) 
           eqi  sigl.fs_params sigr.fs_params in
        Mpv2.check_glob geqi;
        let ml, mr = EcFol.mleft, EcFol.mright in
        let eq_params = 
          f_eqparams fl sigl.fs_params ml fr sigr.fs_params mr in
        let eq_res = f_eqres fl sigl.fs_ret ml fr sigr.fs_ret mr in
        let pre = f_and eq_params (Mpv2.to_form ml mr geqi inv) in
        let post = f_and eq_res (Mpv2.to_form ml mr eqo inv) in
        geqi, f_equivF pre fl fr post
      with EqObsInError ->
        if not (Mpv2.subset eqo eqg) then raise EqObsInError;
        let inv = Mpv2.to_form mleft mright eqg inv in
        eqg, mk_inv_spec env inv fl fr
    end
  | _, _ -> raise EqObsInError 
 
(*
let t_eqobs_inF finfo eqo inv g =
  let env,hyps,concl = get_goal_e g in
  let ef = destr_equivF concl in
  let fl = NormMp.norm_xpath env ef.ef_fl in
  let fr = NormMp.norm_xpath env ef.ef_fr in
  match Fun.by_xpath fl env, Fun.by_xpath fr env with
  | FBabs _, FBabs _ ->
    t_equivF_abs (Mpv2.to_post mleft mright eqo inv) g
  | F 
*)    
    
    



  
