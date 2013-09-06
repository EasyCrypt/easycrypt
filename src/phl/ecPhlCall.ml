(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcBaseLogic
open EcLogic
open EcCorePhl
open EcPV
open EcCoreHiLogic
open EcCoreHiPhl

(* -------------------------------------------------------------------- *)
class rn_hl_call side pr po =
object
  inherit xrule "[hl] call"

  method side : bool option = side
  method pre  : form = pr
  method post : form = po
end

let rn_hl_call side pr po =
  RN_xtd (new rn_hl_call side pr po :> xrule)

(* -------------------------------------------------------------------- *)
let wp_asgn_call env m lv res post =
  match lv with
  | None -> post
  | Some lv ->
    let lets = lv_subst m lv res in
      mk_let_of_lv_substs env ([lets],post)

let subst_args_call env m f =
  List.fold_right2 (fun v e s ->
    PVM.add env (pv_loc f v.v_name) m (form_of_expr m e) s)

let t_hoare_call fpre fpost g =
  (* FIXME : check the well formess of the pre and the post ? *)
  let env,_,concl = get_goal_e g in
  let hs = t_as_hoareS concl in
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
  prove_goal_by [f_concl;concl] (rn_hl_call None fpre fpost) g

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
  let bhs = t_as_bdHoareS concl in
  let (lp,f,args),s = s_last_call "call" bhs.bhs_s in
  let m = EcMemory.memory bhs.bhs_m in
  let fsig = (Fun.by_xpath f env).f_sig in

  let f_concl = bdHoare_call_spec fpre fpost f bhs.bhs_cmp bhs.bhs_bd opt_bd in

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
  prove_goal_by [f_concl;concl] (rn_hl_call None fpre fpost) g

let t_equiv_call fpre fpost g =
  (* FIXME : check the well formess of the pre and the post ? *)
  let env,_,concl = get_goal_e g in
  let es = t_as_equivS concl in
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
  prove_goal_by [f_concl;concl] (rn_hl_call None fpre fpost) g

(* TODO generalize the rule for any lossless statement *)
let t_equiv_call1 side fpre fpost g =
  let env,_,concl = get_goal_e g in
  let equiv = t_as_equivS concl in

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
  let post   = f_forall_simpl [(vres, GTty fsig.fs_ret)] post in
  let spre   = PVM.empty in
  let spre   = subst_args_call env me f fsig.fs_params args spre in
  let post   = 
    f_anda_simpl (PVM.subst env spre (Fsubst.f_subst msubst fpre)) post in
  let concl  =
    match side with
    | true  -> { equiv with es_sl = fstmt; es_po = post; }
    | false -> { equiv with es_sr = fstmt; es_po = post; } in
  let concl  = f_equivS_r concl in
  prove_goal_by [fconcl; concl] (rn_hl_call (Some side) fpre fpost) g

(* -------------------------------------------------------------------- *)
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
      penv, fun inv -> EcCorePhl.mk_inv_spec env inv fl fr
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
      tac_sub :=  (fun g -> t_on_firsts t_logic_trivial 2 (EcPhlFun.t_fun inv g));
      fmake inv 
    | CI_upto info -> 
      let bad,p,q,form = process_upto side info g in
      let t_tr = t_or t_assumption t_logic_trivial in
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
