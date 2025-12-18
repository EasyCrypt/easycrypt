(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module PT  = EcProofTerm
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let wp_asgn_call ?mc env lv res post =
  assert (res.m = post.m);
  let m = post.m in
  match lv with
  | None -> post
  | Some lv ->
      let lets = lv_subst m lv res.inv in
      {m;inv=mk_let_of_lv_substs ?mc env ([lets], post.inv)}

let subst_args_call env m e s =
  PVM.add env pv_arg m (ss_inv_of_expr m e).inv s

(* -------------------------------------------------------------------- *)
let wp2_call
  env fpre fpost (lpl,fl,argsl) modil (lpr,fr,argsr) modir post hyps
=
  let ml, mr = post.ml, post.mr in
  let fsigl = (Fun.by_xpath fl env).f_sig in
  let fsigr = (Fun.by_xpath fr env).f_sig in
  (* The wp *)
  let pvresl = pv_res and pvresr = pv_res in
  let vresl = LDecl.fresh_id hyps "result_L" in
  let vresr = LDecl.fresh_id hyps "result_R" in
  let fresl = {ml;mr; inv=f_local vresl fsigl.fs_ret} in
  let fresr = {ml;mr; inv=f_local vresr fsigr.fs_ret} in
  let post = map_ts_inv_left2 (wp_asgn_call ~mc:(ml,mr) env lpl) fresl post in
  let post = map_ts_inv_right2 (wp_asgn_call ~mc:(ml,mr) env lpr) fresr post in
  let s    = PVM.empty in
  let s    = PVM.add env pvresr mr fresr.inv s in
  let s    = PVM.add env pvresl ml fresl.inv s in
  let fpost = map_ts_inv1 (PVM.subst env s) fpost in
  let post = generalize_mod_ts_inv env modil modir (map_ts_inv2 f_imp_simpl fpost post) in
  let post = map_ts_inv1
    (f_forall_simpl
      [(vresl, GTty fsigl.fs_ret);
       (vresr, GTty fsigr.fs_ret)])
      post in
  let spre = subst_args_call env ml (e_tuple argsl) PVM.empty in
  let spre = subst_args_call env mr (e_tuple argsr) spre in
  map_ts_inv2 f_anda_simpl (map_ts_inv1 (PVM.subst env spre) fpre) post

(* -------------------------------------------------------------------- *)
let t_hoare_call fpre fpost tc =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_hoareS tc in
  let (lp,f,args),s = tc1_last_call tc hs.hs_s in
  let m = EcMemory.memory hs.hs_m in
  let fsig = (Fun.by_xpath f env).f_sig in
  (* The function satisfies the specification *)
  let f_concl = f_hoareF fpre f fpost in
  (* substitute memories *)
  let fpre = (ss_inv_rebind fpre m) in
  let fpost = (ss_inv_rebind fpost m) in
  (* The wp *)
  let pvres = pv_res in
  let vres = EcIdent.create "result" in
  let fres = {m;inv=f_local vres fsig.fs_ret} in
  let post = wp_asgn_call env lp fres (hs_po hs) in
  let fpost = map_ss_inv2 (PVM.subst1 env pvres m) fres fpost in
  let modi = f_write env f in
  let post = generalize_mod_ss_inv env modi (map_ss_inv2 f_imp_simpl fpost post) in
  let post = map_ss_inv1 (f_forall_simpl [(vres, GTty fsig.fs_ret)]) post in
  let spre = subst_args_call env m (e_tuple args) PVM.empty in
  let post = map_ss_inv2 f_anda_simpl (map_ss_inv1 (PVM.subst env spre) fpre) post in
  let concl = f_hoareS (snd hs.hs_m) (hs_pr hs) s post in

  FApi.xmutate1 tc `HlCall [f_concl; concl]


(* -------------------------------------------------------------------- *)
let ehoare_call_pre_post fpre fpost tc =
  let (env, hyps, _) = FApi.tc1_eflat tc in
  let hs = tc1_as_ehoareS tc in
  let (lp,f,args),s = tc1_last_call tc hs.ehs_s in
  let m = EcMemory.memory hs.ehs_m in
  let fpre = ss_inv_rebind fpre m in
  let fpost = ss_inv_rebind fpost m in
  (* Ensure that all asigned variables are locals *)
  let all_loc =
    match lp with
    | None -> true
    | Some(LvVar (v,_)) -> EcTypes.is_loc v
    | Some(LvTuple vs) -> List.for_all (fun (v,_) -> EcTypes.is_loc v) vs in
  if not all_loc then
    tc_error !!tc  "ehoare call core rule: only local variables are supported on the left side of a call";
  (* The wp *)
  let fres =
    match lp with
    | None -> None
    | Some (LvVar (v,ty)) -> Some (f_pvar v ty m)
    | Some (LvTuple vs) -> Some (map_ss_inv f_tuple (List.map (fun (v,ty) -> f_pvar v ty m) vs)) in
  let pvres = pv_res in
  let wppost =
    omap_dfl (fun fres -> map_ss_inv2 (PVM.subst1 env pvres m) fres fpost) fpost fres in
  let fv = PV.fv env m wppost.inv in
  if PV.mem_pv env pv_res fv then
    tc_error !!tc
      "ehoare call core rule: the post condition of the function depend on res but the result is not assigned";

  let spre = subst_args_call env m (e_tuple args) PVM.empty in
  let wppre = map_ss_inv1 (PVM.subst env spre) fpre in
  hyps, env, hs, s, f, wppre, wppost


let t_ehoare_call_core fpre fpost tc =
  let hyps, env, hs, s, f, wppre, wppost = ehoare_call_pre_post fpre fpost tc in
  if not (List.is_empty s.s_node) then
    tc_error !!tc  "ehoare call core rule: only single call statements are accepted";
  if not (EcReduction.ss_inv_alpha_eq hyps (ehs_po hs) wppost) then
    (let env = EcEnv.Memory.push_active_ss hs.ehs_m env in
     let ppe  = EcPrinting.PPEnv.ofenv env in
     tc_error !!tc "ehoare call core rule: wrong post-condition %a instead %a"
       (EcPrinting.pp_form ppe) (ehs_po hs).inv (EcPrinting.pp_form ppe) wppost.inv);

  if not (EcReduction.ss_inv_alpha_eq hyps (ehs_pr hs) wppre) then
    (let env = EcEnv.Memory.push_active_ss hs.ehs_m env in
     let ppe  = EcPrinting.PPEnv.ofenv env in
     tc_error !!tc "ehoare call core rule: wrong pre-condition %a instead %a"
       (EcPrinting.pp_form ppe) (ehs_pr hs).inv (EcPrinting.pp_form ppe) wppre.inv);

  (* The function satisfies the specification *)
  let f_concl = f_eHoareF fpre f fpost in
  FApi.xmutate1 tc `HlCall [f_concl]


let t_ehoare_call fpre fpost tc =
  let _, _, _, s, _, wppre, _ = ehoare_call_pre_post fpre fpost tc in
  let tcenv =
    EcPhlApp.t_ehoare_app (EcMatching.Zipper.cpos (List.length s.s_node)) wppre tc in
  let tcenv = FApi.t_swap_goals 0 1 tcenv in
  FApi.t_sub [t_ehoare_call_core fpre fpost; t_id] tcenv

let t_ehoare_call_concave f fpre fpost tc =
  let _, _, _, s, _, wppre, wppost = ehoare_call_pre_post fpre fpost tc in
  let tcenv =
    EcPhlApp.t_ehoare_app (EcMatching.Zipper.cpos (List.length s.s_node))
     (map_ss_inv2 (fun wppre f -> f_app_simpl f [wppre] txreal) wppre f) tc in
  let tcenv = FApi.t_swap_goals 0 1 tcenv in
  let t_call =
    FApi.t_seqsub (EcPhlConseq.t_ehoareS_concave f wppre wppost)
      [ t_id;
        t_id;
        t_id;
        t_ehoare_call_core fpre fpost]
  in

  FApi.t_sub [t_call; t_id] tcenv

(* -------------------------------------------------------------------- *)
let bdhoare_call_spec pf fpre fpost f cmp bd opt_bd =
  let msg =
    "optional bound parameter not allowed for upper-bounded judgements" in

  match cmp, opt_bd with
  | FHle, Some _  -> tc_error pf "%s" msg
  | FHle, None    -> f_bdHoareF fpre f fpost FHle bd
  | FHeq, Some bd -> f_bdHoareF fpre f fpost FHeq bd
  | FHeq, None    -> f_bdHoareF fpre f fpost FHeq bd
  | FHge, Some bd -> f_bdHoareF fpre f fpost FHge bd
  | FHge, None    -> f_bdHoareF fpre f fpost FHge bd

(* -------------------------------------------------------------------- *)
let t_bdhoare_call fpre fpost opt_bd tc =
  let env = FApi.tc1_env tc in
  let bhs = tc1_as_bdhoareS tc in
  let (lp,f,args),s = tc1_last_call tc bhs.bhs_s in
  let m =  fpre.m in
  let fsig = (Fun.by_xpath f env).f_sig in
  let bhs_bd = ss_inv_rebind (bhs_bd bhs) m in
  let bhs_po = ss_inv_rebind (bhs_po bhs) m in
  let bhs_pr = ss_inv_rebind (bhs_pr bhs) m in

  (* The function satisfies the specification *)
  let f_concl =
    bdhoare_call_spec !!tc fpre fpost f bhs.bhs_cmp bhs_bd opt_bd in

  (* The wp *)
  let pvres = pv_res in
  let vres = EcIdent.create "result" in
  let fres = {m;inv=f_local vres fsig.fs_ret} in
  let post = wp_asgn_call env lp fres bhs_po in
  let fpost = map_ss_inv2 (PVM.subst1 env pvres m) fres fpost in
  let modi = f_write env f in
  let post =
    match bhs.bhs_cmp with
    | FHle -> map_ss_inv2 f_imp_simpl   post fpost
    | FHge -> map_ss_inv2 f_imp_simpl  fpost  post

    | FHeq when f_equal bhs_bd.inv f_r0 ->
        map_ss_inv2 f_imp_simpl post fpost

    | FHeq when f_equal bhs_bd.inv f_r1 ->
        map_ss_inv2 f_imp_simpl  fpost post

    | FHeq -> map_ss_inv2 f_iff_simpl fpost  post in

  let post = generalize_mod_ss_inv env modi post in
  let post = map_ss_inv1 (f_forall_simpl [(vres, GTty fsig.fs_ret)]) post in
  let spre = subst_args_call env m (e_tuple args) PVM.empty in
  let post = map_ss_inv2 f_anda_simpl (map_ss_inv1 (PVM.subst env spre) fpre) post in

  (* most of the above code is duplicated from t_hoare_call *)
  let concl =
    let _,mt = bhs.bhs_m in
    match bhs.bhs_cmp, opt_bd with
    | FHle, None ->
        f_hoareS mt bhs_pr s post
    | FHeq, Some bd ->
        f_bdHoareS mt bhs_pr s post bhs.bhs_cmp (map_ss_inv2 f_real_div bhs_bd bd)
    | FHeq, None ->
        f_bdHoareS mt bhs_pr s post bhs.bhs_cmp {m;inv=f_r1}
    | FHge, Some bd ->
        f_bdHoareS mt bhs_pr s post bhs.bhs_cmp (map_ss_inv2 f_real_div bhs_bd bd)
    | FHge, None ->
        f_bdHoareS mt bhs_pr s post FHeq {m;inv=f_r1}
    | _, _ -> assert false
  in

  FApi.xmutate1 tc `HlCall [f_concl; concl]

(* -------------------------------------------------------------------- *)
let t_equiv_call fpre fpost tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let es = tc1_as_equivS tc in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  let fpre = ts_inv_rebind fpre ml mr in
  let fpost = ts_inv_rebind fpost ml mr in

  let (lpl,fl,argsl),sl = tc1_last_call tc es.es_sl in
  let (lpr,fr,argsr),sr = tc1_last_call tc es.es_sr in
  (* The functions satisfy their specification *)
  let f_concl = f_equivF fpre fl fr fpost in
  let modil = f_write env fl in
  let modir = f_write env fr in
  (* The wp *)
  let post =
    wp2_call env fpre fpost
      (lpl,fl,argsl) modil (lpr,fr,argsr) modir
      (es_po es) hyps
  in
  let concl =
    f_equivS (snd es.es_ml) (snd es.es_mr) (es_pr es) sl sr post in

  FApi.xmutate1 tc `HlCall [f_concl; concl]

(* -------------------------------------------------------------------- *)
let t_equiv_call1 side fpre fpost tc =
  let env = FApi.tc1_env tc in
  let equiv = tc1_as_equivS tc in
  let ml, mr = fst equiv.es_ml, fst equiv.es_mr in
  let mtl, mtr = snd equiv.es_ml, snd equiv.es_mr in

  let (me, stmt) =
    match side with
    | `Left  -> (EcMemory.memory equiv.es_ml, equiv.es_sl)
    | `Right -> (EcMemory.memory equiv.es_mr, equiv.es_sr)
  in
  let wp_asgn_call_side env lv = sideif side
    (map_ts_inv_left2 (wp_asgn_call ~mc:(ml,mr) env lv))
    (map_ts_inv_right2 (wp_asgn_call ~mc:(ml,mr) env lv))
  in
  let generalize_mod_side = sideif side
    generalize_mod_left generalize_mod_right in
  let ss_inv_generalize_other_side inv = sideif side
    (ss_inv_generalize_right inv mr) (ss_inv_generalize_left inv ml) in

  let (lp, f, args), fstmt = tc1_last_call tc stmt in
  let fsig = (Fun.by_xpath f env).f_sig in

  (* The function satisfies its specification *)
  let fconcl = f_bdHoareF fpre f fpost FHeq {m=fpost.m; inv=f_r1} in

  (* WP *)
  let pvres  = pv_res in
  let vres   = LDecl.fresh_id (FApi.tc1_hyps tc) "result" in
  let fres   = {ml;mr;inv=f_local vres fsig.fs_ret} in
  let post   = wp_asgn_call_side env lp fres (es_po equiv) in
  let subst  = PVM.add env pvres me fres.inv PVM.empty in
  let fpost  = ss_inv_generalize_other_side (ss_inv_rebind fpost me) in
  let fpre   = ss_inv_generalize_other_side (ss_inv_rebind fpre me) in
  let fpost  = map_ts_inv1 (PVM.subst env subst) fpost in
  let modi   = f_write env f in
  let post   = map_ts_inv2 f_imp_simpl fpost post in
  let post   = generalize_mod_side env modi post in
  let post   = map_ts_inv1 (f_forall_simpl [(vres, GTty fsig.fs_ret)]) post in
  let spre   = PVM.empty in
  let spre   = subst_args_call env me (e_tuple args) spre in
  let post   =
    map_ts_inv2 f_anda_simpl (map_ts_inv1 (PVM.subst env spre) fpre) post in
  let concl  =
    match side with
    | `Left  -> f_equivS mtl mtr (es_pr equiv) fstmt equiv.es_sr post
    | `Right -> f_equivS mtl mtr (es_pr equiv) equiv.es_sl fstmt post in

  FApi.xmutate1 tc `HlCall [fconcl; concl]

(* -------------------------------------------------------------------- *)
let call_error env tc f1 f2 =
  tc_error_lazy !!tc (fun fmt ->
      let ppe = EcPrinting.PPEnv.ofenv env in
      Format.fprintf fmt
        "call cannot be used with a lemma referring to `%a': \
         the last statement is a call to `%a'"
        (EcPrinting.pp_funname ppe) f1
        (EcPrinting.pp_funname ppe) f2)

let t_call side ax tc =
  let env   = FApi.tc1_env  tc in
  let hyps, concl = FApi.tc1_flat tc in
  let ax = EcReduction.h_red_until EcReduction.full_red hyps ax in
  match ax.f_node, concl.f_node with
  | FhoareF hf, FhoareS hs ->
      let (_, f, _), _ = tc1_last_call tc hs.hs_s in
      if not (EcEnv.NormMp.x_equal env hf.hf_f f) then
        call_error env tc hf.hf_f f;
      t_hoare_call (hf_pr hf) (hf_po hf) tc

  | FeHoareF hf, FeHoareS hs ->
      let (_, f, _), _ = tc1_last_call tc hs.ehs_s in
      if not (EcEnv.NormMp.x_equal env hf.ehf_f f) then
        call_error env tc hf.ehf_f f;
      t_ehoare_call (ehf_pr hf) (ehf_po hf) tc

  | FbdHoareF hf, FbdHoareS hs ->
      let (_, f, _), _ = tc1_last_call tc hs.bhs_s in
      if not (EcEnv.NormMp.x_equal env hf.bhf_f f) then
        call_error env tc hf.bhf_f f;
      t_bdhoare_call (bhf_pr hf) (bhf_po hf) None tc

  | FequivF ef, FequivS es ->
      let (_, fl, _), _ = tc1_last_call tc es.es_sl in
      let (_, fr, _), _ = tc1_last_call tc es.es_sr in
      if not (EcEnv.NormMp.x_equal env ef.ef_fl fl) ||
         not (EcEnv.NormMp.x_equal env ef.ef_fr fr) then
        tc_error_lazy !!tc (fun fmt ->
          let ppe = EcPrinting.PPEnv.ofenv env in
            Format.fprintf fmt
              "call cannot be used with a lemma referring to `%a/%a': \
               the last statement is a call to `%a/%a'"
              (EcPrinting.pp_funname ppe) ef.ef_fl
              (EcPrinting.pp_funname ppe) ef.ef_fr
              (EcPrinting.pp_funname ppe) fl
              (EcPrinting.pp_funname ppe) fr);
      t_equiv_call (ef_pr ef) (ef_po ef) tc

  | FbdHoareF hf, FequivS _ ->
      let side =
        match side with
        | None -> tc_error !!tc "call: a side {1|2} should be provided"
        | Some side -> side
      in
        t_equiv_call1 side (bhf_pr hf) (bhf_po hf) tc

  | _, _ -> tc_error !!tc "call: invalid goal shape"

(* -------------------------------------------------------------------- *)
let mk_inv_spec (_pf : proofenv) env inv fl fr =
  let ml, mr = inv.ml, inv.mr in
  match NormMp.is_abstract_fun fl env with
  | true ->
    let (topl, _, _, sigl),
      (topr, _, _  , sigr) = EcLowPhlGoal.abstract_info2 env fl fr in
    let eqglob = ts_inv_eqglob topl ml topr mr in
    let lpre = [eqglob;inv] in
    let eq_params =
      ts_inv_eqparams
        sigl.fs_arg sigl.fs_anames ml
        sigr.fs_arg sigr.fs_anames mr in
    let eq_res = ts_inv_eqres sigl.fs_ret ml sigr.fs_ret mr in
    let pre    = map_ts_inv f_ands (eq_params::lpre) in
    let post   = map_ts_inv f_ands [eq_res; eqglob; inv] in
      f_equivF pre fl fr post

  | false ->
      let defl = EcEnv.Fun.by_xpath fl env in
      let defr = EcEnv.Fun.by_xpath fr env in
      let sigl, sigr = defl.f_sig, defr.f_sig in
      let testty =
           EcReduction.EqTest.for_type env sigl.fs_arg sigr.fs_arg
        && EcReduction.EqTest.for_type env sigl.fs_ret sigr.fs_ret
      in

      if not testty then raise EqObsInError;
      let eq_params =
        ts_inv_eqparams
          sigl.fs_arg sigl.fs_anames ml
          sigr.fs_arg sigr.fs_anames mr in
      let eq_res = ts_inv_eqres sigl.fs_ret ml sigr.fs_ret mr in
      let pre = map_ts_inv2 f_and eq_params inv in
      let post = map_ts_inv2 f_and eq_res inv in
        f_equivF pre fl fr post

let process_call side info tc =
  let process_spec tc side pre post =
    let (hyps, concl) = FApi.tc1_flat tc in
      match concl.f_node, side with
      | FhoareS hs, None ->
          let (_,f,_) = fst (tc1_last_call tc hs.hs_s) in
          let m = (EcIdent.create "&hr") in
          let penv, qenv = LDecl.hoareF m f hyps in
          let pre  = TTC.pf_process_form !!tc penv tbool pre  in
          let post = TTC.pf_process_form !!tc qenv tbool post in
          f_hoareF {m;inv=pre} f {m;inv=post}

      | FbdHoareS bhs, None ->
          let (_,f,_) = fst (tc1_last_call tc bhs.bhs_s) in
          let m = (EcIdent.create "&hr") in
          let penv, qenv = LDecl.hoareF m f hyps in
          let pre  = TTC.pf_process_form !!tc penv tbool pre  in
          let post = TTC.pf_process_form !!tc qenv tbool post in
          let bd = ss_inv_rebind (bhs_bd bhs) m in
          bdhoare_call_spec !!tc {m;inv=pre} {m;inv=post} f bhs.bhs_cmp bd None

      | FeHoareS hs, None ->
          let (_,f,_) = fst (tc1_last_call tc hs.ehs_s) in
          let m = (EcIdent.create "&hr") in
          let penv, qenv = LDecl.hoareF m f hyps in
          let pre  = TTC.pf_process_form !!tc penv txreal pre  in
          let post = TTC.pf_process_form !!tc qenv txreal post in
          f_eHoareF {m;inv=pre} f {m;inv=post}

      | FbdHoareS _, Some _
      | FhoareS  _, Some _ ->
          tc_error !!tc "side can only be given for prhl judgements"

      | FequivS es, None ->
          let (_,fl,_) = fst (tc1_last_call tc es.es_sl) in
          let (_,fr,_) = fst (tc1_last_call tc es.es_sr) in
          let (ml, mr) = (EcIdent.create "&1", EcIdent.create "&2") in
          let penv, qenv = LDecl.equivF ml mr fl fr hyps in
          let pre  = TTC.pf_process_form !!tc penv tbool pre  in
          let post = TTC.pf_process_form !!tc qenv tbool post in
          f_equivF {ml;mr;inv=pre} fl fr {ml;mr;inv=post}

      | FequivS es, Some side ->
          let fstmt = sideif side es.es_sl es.es_sr in
          let m = sideif side (EcIdent.create "&1") (EcIdent.create "&2") in
          let (_,f,_) = fst (tc1_last_call tc fstmt) in
          let penv, qenv = LDecl.hoareF m f hyps in
          let pre  = TTC.pf_process_form !!tc penv tbool pre  in
          let post = TTC.pf_process_form !!tc qenv tbool post in
          f_bdHoareF {m;inv=pre} f {m;inv=post} FHeq {m;inv=f_r1}

      | _ -> tc_error !!tc "the conclusion is not a hoare or an equiv" in

  let process_inv tc side inv =
    if not (is_none side) then
      tc_error !!tc "cannot specify side for call with invariants";

    let hyps, concl = FApi.tc1_flat tc in
    match concl.f_node with
    | FhoareS hs ->
        let m = fst hs.hs_m in
        let (_,f,_) = fst (tc1_last_call tc hs.hs_s) in
        let me = EcMemory.abstract m in
        let hyps = LDecl.push_active_ss me hyps in
        let inv = TTC.pf_process_form !!tc hyps tbool inv in
        let inv = {m; inv} in
        (f_hoareF inv f inv, Inv_ss inv)

    | FeHoareS hs ->
        let m = fst hs.ehs_m in
        let (_,f,_) = fst (tc1_last_call tc hs.ehs_s) in
        let me = EcMemory.abstract m in
        let hyps = LDecl.push_active_ss me hyps in
        let inv = TTC.pf_process_form !!tc hyps txreal inv in
        let inv = {m; inv} in
        (f_eHoareF inv f inv, Inv_ss inv)

    | FbdHoareS bhs ->
      let m = fst bhs.bhs_m in
      let (_,f,_) = fst (tc1_last_call tc bhs.bhs_s) in
      let me = EcMemory.abstract m in
      let hyps = LDecl.push_active_ss me hyps in
      let inv = TTC.pf_process_form !!tc hyps tbool inv in
      let inv = {m; inv} in
      let f = bdhoare_call_spec !!tc inv inv f bhs.bhs_cmp (bhs_bd bhs) None in
      (f, Inv_ss inv)

    | FequivS es ->
      let ml, mr = fst es.es_ml, fst es.es_mr in
      let (_,fl,_) = fst (tc1_last_call tc es.es_sl) in
      let (_,fr,_) = fst (tc1_last_call tc es.es_sr) in
      let mel, mer = EcMemory.abstract ml, EcMemory.abstract mr in
      let hyps = LDecl.push_active_ts mel mer hyps in
      let env  = LDecl.toenv hyps in
      let inv = TTC.pf_process_form !!tc hyps tbool inv in
      let inv = {ml;mr; inv} in
      (mk_inv_spec !!tc env inv fl fr, Inv_ts inv)

    | _ -> tc_error !!tc "the conclusion is not a hoare or an equiv" in

  let process_upto tc side info =
    if not (is_none side) then
      tc_error !!tc "cannot specify side for call with invariants";
    let env, _, concl = FApi.tc1_eflat tc in
      match concl.f_node with
      | FequivS es ->
        let ml, mr = fst es.es_ml, fst es.es_mr in
        let (_,fl,_) = fst (tc1_last_call tc es.es_sl) in
        let (_,fr,_) = fst (tc1_last_call tc es.es_sr) in
        let bad,invP,invQ = EcPhlFun.process_fun_upto_info info tc in
        let bad2 = ss_inv_generalize_as_right bad ml mr in
        let invP = ts_inv_rebind invP ml mr in
        let invQ = ts_inv_rebind invQ ml mr in
        let (topl,fl,_,sigl),
            (topr,fr,_  ,sigr) = EcLowPhlGoal.abstract_info2 env fl fr in
        let eqglob = ts_inv_eqglob topl ml topr mr in
        let lpre = [eqglob;invP] in
        let eq_params =
          ts_inv_eqparams
            sigl.fs_arg sigl.fs_anames ml
            sigr.fs_arg sigr.fs_anames mr in
        let eq_res = ts_inv_eqres sigl.fs_ret ml sigr.fs_ret mr in
        let pre    = map_ts_inv3 f_if_simpl bad2 invQ (map_ts_inv f_ands (eq_params::lpre)) in
        let post   = map_ts_inv3 f_if_simpl bad2 invQ (map_ts_inv f_ands [eq_res;eqglob;invP]) in
        (bad,invP,invQ, f_equivF pre fl fr post)

    | _ -> tc_error !!tc "the conclusion is not an equiv" in

  let subtactic = ref t_id in

  let process_cut tc info =
    match info with
    | CI_spec (pre, post) ->
      process_spec tc side pre post
    | CI_inv inv ->
      let f, inv = process_inv tc side inv in
      subtactic := (fun tc ->
        FApi.t_firsts t_trivial 2 (EcPhlFun.t_fun inv tc));
      f

    | CI_upto info ->
      let bad, p, q, form = process_upto tc side info in
      let t_tr = FApi.t_or (t_assumption `Conv) t_trivial in
      subtactic := (fun tc ->
        FApi.t_firsts t_tr 3 (EcPhlFun.t_equivF_abs_upto bad p q tc));
      form

  in

  let pt = PT.tc1_process_full_pterm_cut ~prcut:(process_cut tc) tc info
  in

  let pt =
    let rec doit pt =
      match TTC.destruct_product ~reduce:true (FApi.tc1_hyps tc) pt.PT.ptev_ax with
      | None   -> pt
      | Some _ -> doit (EcProofTerm.apply_pterm_to_hole pt)
    in doit pt in

  let pt, ax =
    if not (PT.can_concretize pt.PT.ptev_env) then
      tc_error !!tc "cannot infer all placeholders";
    PT.concretize pt in

  FApi.t_seqsub
    (t_call side ax)
    [FApi.t_seqs
       [EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt;
        !subtactic; t_trivial];
     t_id]
    tc

(* -------------------------------------------------------------------- *)
let process_call_concave (fc, info) tc =
  let fc =
    let (hyps, concl) = FApi.tc1_flat tc in
    match concl.f_node  with
    | FeHoareS hs ->
      let env = LDecl.push_active_ss hs.ehs_m hyps in
      {m=fst hs.ehs_m;inv=TTC.pf_process_form !!tc env (tfun txreal txreal) fc}

    | _ -> tc_error !!tc "the conclusion is not a ehoare" in

  let process_spec tc =
    let _, concl = FApi.tc1_flat tc in
      match concl.f_node  with
      | FeHoareS hs ->
          let (_,f,_) = fst (tc1_last_call tc hs.ehs_s) in
          (txreal, fun pre post -> f_eHoareF pre f post)

      | _ -> tc_error !!tc "the conclusion is not a ehoare" in

  let process_inv tc =
      let _, concl = FApi.tc1_flat tc in
    match concl.f_node with
    | FeHoareS hs ->
        let (_,f,_) = fst (tc1_last_call tc hs.ehs_s) in
        (txreal, fun inv -> f_eHoareF inv f inv)

    | _ -> tc_error !!tc "the conclusion is not a ehoare" in

  let subtactic = ref t_id in

  let process_cut tc info =
    match info with
    | CI_spec (pre, post) ->
      let ty,fmake = process_spec tc in
      let _, pre = TTC.tc1_process_Xhl_form tc ty pre in
      let _, post = TTC.tc1_process_Xhl_form tc ty post in
      fmake pre post

    | CI_inv inv ->
      let ty, fmake = process_inv tc in
      let _, inv = TTC.tc1_process_Xhl_form tc ty inv in
      subtactic := (fun tc ->
        FApi.t_firsts t_trivial 2 (EcPhlFun.t_fun (Inv_ss inv) tc));
      fmake inv

    | _ ->
        tc_error !!tc "cannot supply additional information for call /"

  in

  let pt = PT.tc1_process_full_pterm_cut ~prcut:(process_cut tc) tc info
  in

  let pt =
    let rec doit pt =
      match TTC.destruct_product ~reduce:true (FApi.tc1_hyps tc) pt.PT.ptev_ax with
      | None   -> pt
      | Some _ -> doit (EcProofTerm.apply_pterm_to_hole pt)
    in doit pt in

  let pt, ax =
    if not (PT.can_concretize pt.PT.ptev_env) then
      tc_error !!tc "cannot infer all placeholders";
    PT.concretize pt in

  let t_call ax tc =
    let (env, _, concl) = FApi.tc1_eflat tc in
    match ax.f_node, concl.f_node with
    | FeHoareF hf, FeHoareS hs ->
      let (_, f, _), _ = tc1_last_call tc hs.ehs_s in
      if not (EcEnv.NormMp.x_equal env hf.ehf_f f) then
        call_error env tc hf.ehf_f f;
      t_ehoare_call_concave fc (ehf_pr hf) (ehf_po hf) tc
    | _, _ -> tc_error !!tc "call: invalid goal shape" in

  FApi.t_seqsub
    (t_call ax)
    [ EcPhlConseq.t_concave_incr;
      t_trivial; (* pre *)
      t_trivial; (* post *)
      FApi.t_seqs
        [EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt;
         !subtactic; t_trivial];
      t_id]
    tc
