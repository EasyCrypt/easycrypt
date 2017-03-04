(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module PT  = EcProofTerm
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let wp_asgn_call env m lv res post =
  match lv with
  | None -> post
  | Some lv ->
      let lets = lv_subst m lv res in
      mk_let_of_lv_substs env ([lets], post)

let subst_args_call env m f e s =
  PVM.add env (pv_arg f) m (form_of_expr m e) s

(* -------------------------------------------------------------------- *)
let wp2_call
  env fpre fpost (lpl,fl,argsl) modil (lpr,fr,argsr) modir ml mr post hyps
=
  let fsigl = (Fun.by_xpath fl env).f_sig in
  let fsigr = (Fun.by_xpath fr env).f_sig in
  (* The wp *)
  let pvresl = pv_res fl and pvresr = pv_res fr in
  let vresl = LDecl.fresh_id hyps "result_L" in
  let vresr = LDecl.fresh_id hyps "result_R" in
  let fresl = f_local vresl fsigl.fs_ret in
  let fresr = f_local vresr fsigr.fs_ret in
  let post = wp_asgn_call env ml lpl fresl post in
  let post = wp_asgn_call env mr lpr fresr post in
  let s    = PVM.empty in
  let s    = PVM.add env pvresr mr fresr s in
  let s    = PVM.add env pvresl ml fresl s in
  let fpost = PVM.subst env s fpost in
  let post = generalize_mod env mr modir (f_imp_simpl fpost post) in
  let post = generalize_mod env ml modil post in
  let post =
    f_forall_simpl
      [(vresl, GTty fsigl.fs_ret);
       (vresr, GTty fsigr.fs_ret)]
      post in
  let spre = subst_args_call env ml fl (e_tuple argsl) PVM.empty in
  let spre = subst_args_call env mr fr (e_tuple argsr) spre in
  f_anda_simpl (PVM.subst env spre fpre) post

(* -------------------------------------------------------------------- *)
let t_hoare_call fpre fpost tc =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_hoareS tc in
  let (lp,f,args),s = tc1_last_call tc hs.hs_s in
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
  let spre = subst_args_call env m f (e_tuple args) PVM.empty in
  let post = f_anda_simpl (PVM.subst env spre fpre) post in
  let concl = f_hoareS_r { hs with hs_s = s; hs_po=post} in

  FApi.xmutate1 tc `HlCall [f_concl; concl]

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
  let m = EcMemory.memory bhs.bhs_m in
  let fsig = (Fun.by_xpath f env).f_sig in
  let f_concl =
    bdhoare_call_spec !!tc fpre fpost f bhs.bhs_cmp bhs.bhs_bd opt_bd in

  (* The wp *)
  let pvres = pv_res f in
  let vres = EcIdent.create "result" in
  let fres = f_local vres fsig.fs_ret in
  let post = wp_asgn_call env m lp fres bhs.bhs_po in
  let fpost = PVM.subst1 env pvres m fres fpost in
  let modi = f_write env f in
  let post = generalize_mod env m modi (f_imp_simpl fpost post) in
  let post = f_forall_simpl [(vres, GTty fsig.fs_ret)] post in
  let spre = subst_args_call env m f (e_tuple args) PVM.empty in
  let post = f_anda_simpl (PVM.subst env spre fpre) post in

  (* most of the above code is duplicated from t_hoare_call *)
  let concl = match bhs.bhs_cmp, opt_bd with
    | FHle, None ->
        f_hoareS bhs.bhs_m bhs.bhs_pr s post
    | FHeq, Some bd ->
        f_bdHoareS_r { bhs with
          bhs_s = s; bhs_po = post; bhs_bd = f_real_div bhs.bhs_bd bd; }
    | FHeq, None ->
        f_bdHoareS_r { bhs with
          bhs_s = s; bhs_po = post; bhs_bd = f_r1; }
    | FHge, Some bd ->
        f_bdHoareS_r { bhs with
          bhs_s = s; bhs_po = post; bhs_bd = f_real_div bhs.bhs_bd bd; }
    | FHge, None ->
        f_bdHoareS_r { bhs with
          bhs_s = s; bhs_po = post; bhs_cmp = FHeq; bhs_bd = f_r1; }
    | _, _ -> assert false
  in

  FApi.xmutate1 tc `HlCall [f_concl; concl]

(* -------------------------------------------------------------------- *)
let t_equiv_call fpre fpost tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let es = tc1_as_equivS tc in
  let (lpl,fl,argsl),sl = tc1_last_call tc es.es_sl in
  let (lpr,fr,argsr),sr = tc1_last_call tc es.es_sr in
  let ml = EcMemory.memory es.es_ml in
  let mr = EcMemory.memory es.es_mr in
  (* The functions satisfy their specification *)
  let f_concl = f_equivF fpre fl fr fpost in
  let modil = f_write env fl in
  let modir = f_write env fr in
  (* The wp *)
  let post =
    wp2_call env fpre fpost
      (lpl,fl,argsl) modil (lpr,fr,argsr) modir
      ml mr es.es_po hyps
  in
  let concl =
    f_equivS_r { es with es_sl = sl; es_sr = sr; es_po = post; } in

  FApi.xmutate1 tc `HlCall [f_concl; concl]

(* -------------------------------------------------------------------- *)
let t_equiv_call1 side fpre fpost tc =
  let env = FApi.tc1_env tc in
  let equiv = tc1_as_equivS tc in

  let (me, stmt) =
    match side with
    | `Left  -> (EcMemory.memory equiv.es_ml, equiv.es_sl)
    | `Right -> (EcMemory.memory equiv.es_mr, equiv.es_sr)
  in

  let (lp, f, args), fstmt = tc1_last_call tc stmt in
  let fsig = (Fun.by_xpath f env).f_sig in

  (* The function satisfies its specification *)
  let fconcl = f_bdHoareF fpre f fpost FHeq f_r1 in

  (* WP *)
  let pvres  = pv_res f in
  let vres   = LDecl.fresh_id (FApi.tc1_hyps tc) "result" in
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
  let spre   = subst_args_call env me f (e_tuple args) spre in
  let post   =
    f_anda_simpl (PVM.subst env spre (Fsubst.f_subst msubst fpre)) post in
  let concl  =
    match side with
    | `Left  -> { equiv with es_sl = fstmt; es_po = post; }
    | `Right -> { equiv with es_sr = fstmt; es_po = post; } in
  let concl  = f_equivS_r concl in

  FApi.xmutate1 tc `HlCall [fconcl; concl]

(* -------------------------------------------------------------------- *)
let mk_inv_spec (_pf : proofenv) env inv fl fr =
  match NormMp.is_abstract_fun fl env with
  | true ->
    let (topl, _, oil, sigl),
      (topr, _, _  , sigr) = EcLowPhlGoal.abstract_info2 env fl fr in
    let eqglob = f_eqglob topl mleft topr mright in
    let lpre = if oil.oi_in then [eqglob;inv] else [inv] in
    let eq_params =
      f_eqparams
        fl sigl.fs_arg sigl.fs_anames mleft
        fr sigr.fs_arg sigr.fs_anames mright in
    let eq_res = f_eqres fl sigl.fs_ret mleft fr sigr.fs_ret mright in
    let pre    = f_ands (eq_params::lpre) in
    let post   = f_ands [eq_res; eqglob; inv] in
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
        f_eqparams
          fl sigl.fs_arg sigl.fs_anames mleft
          fr sigr.fs_arg sigr.fs_anames mright in
      let eq_res = f_eqres fl sigl.fs_ret mleft fr sigr.fs_ret mright in
      let pre = f_and eq_params inv in
      let post = f_and eq_res inv in
        f_equivF pre fl fr post

let process_call side info tc =
  let process_spec tc side =
    let (hyps, concl) = FApi.tc1_flat tc in
      match concl.f_node, side with
      | FhoareS hs, None ->
          let (_,f,_) = fst (tc1_last_call tc hs.hs_s) in
          let penv, qenv = LDecl.hoareF f hyps in
          (penv, qenv, fun pre post -> f_hoareF pre f post)

      | FbdHoareS bhs, None ->
          let (_,f,_) = fst (tc1_last_call tc bhs.bhs_s) in
          let penv, qenv = LDecl.hoareF f hyps in
          (penv, qenv, fun pre post ->
            bdhoare_call_spec !!tc pre post f bhs.bhs_cmp bhs.bhs_bd None)

      | FbdHoareS _, Some _ | FhoareS _, Some _ ->
          tc_error !!tc "side can only be given for prhl judgements"

      | FequivS es, None ->
          let (_,fl,_) = fst (tc1_last_call tc es.es_sl) in
          let (_,fr,_) = fst (tc1_last_call tc es.es_sr) in
          let penv, qenv = LDecl.equivF fl fr hyps in
          (penv, qenv, fun pre post -> f_equivF pre fl fr post)

      | FequivS es, Some side ->
          let fstmt = sideif side es.es_sl es.es_sr in
          let (_,f,_) = fst (tc1_last_call tc fstmt) in
          let penv, qenv = LDecl.hoareF f hyps in
          (penv, qenv, fun pre post -> f_bdHoareF pre f post FHeq f_r1)

      | _ -> tc_error !!tc "the conclusion is not a hoare or a equiv" in

  let process_inv tc side =
    if not (is_none side) then
      tc_error !!tc "cannot specify side for call with invariants";

    let hyps, concl = FApi.tc1_flat tc in
    match concl.f_node with
    | FhoareS hs ->
        let (_,f,_) = fst (tc1_last_call tc hs.hs_s) in
        let penv = LDecl.inv_memenv1 hyps in
        (penv, fun inv -> f_hoareF inv f inv)

    | FbdHoareS bhs ->
      let (_,f,_) = fst (tc1_last_call tc bhs.bhs_s) in
      let penv = LDecl.inv_memenv1 hyps in
      (penv, fun inv -> bdhoare_call_spec !!tc inv inv f bhs.bhs_cmp bhs.bhs_bd None)

    | FequivS es ->
      let (_,fl,_) = fst (tc1_last_call tc es.es_sl) in
      let (_,fr,_) = fst (tc1_last_call tc es.es_sr) in
      let penv = LDecl.inv_memenv hyps in
      let env  = LDecl.toenv hyps in
      (penv, fun inv -> mk_inv_spec !!tc env inv fl fr)

    | _ -> tc_error !!tc "the conclusion is not a hoare or an equiv" in

  let process_upto tc side info =
    if not (is_none side) then
      tc_error !!tc "cannot specify side for call with invariants";
    let env, _, concl = FApi.tc1_eflat tc in
      match concl.f_node with
      | FequivS es ->
        let (_,fl,_) = fst (tc1_last_call tc es.es_sl) in
        let (_,fr,_) = fst (tc1_last_call tc es.es_sr) in
        let bad,invP,invQ = EcPhlFun.process_fun_upto_info info tc in
        let (topl,fl,oil,sigl),
            (topr,fr,_  ,sigr) = EcLowPhlGoal.abstract_info2 env fl fr in
        let bad2 = Fsubst.f_subst_mem mhr mright bad in
        let eqglob = f_eqglob topl mleft topr mright in
        let lpre = if oil.oi_in then [eqglob;invP] else [invP] in
        let eq_params =
          f_eqparams
            fl sigl.fs_arg sigl.fs_anames mleft
            fr sigr.fs_arg sigr.fs_anames mright in
        let eq_res = f_eqres fl sigl.fs_ret mleft fr sigr.fs_ret mright in
        let pre    = f_if_simpl bad2 invQ (f_ands (eq_params::lpre)) in
        let post   = f_if_simpl bad2 invQ (f_ands [eq_res;eqglob;invP]) in
        (bad,invP,invQ, f_equivF pre fl fr post)

    | _ -> tc_error !!tc "the conclusion is not an equiv" in

  let subtactic = ref t_id in

  let process_cut tc info =
    match info with
    | CI_spec (pre, post) ->
      let penv,qenv,fmake = process_spec tc side in
      let pre  = TTC.pf_process_form !!tc penv tbool pre  in
      let post = TTC.pf_process_form !!tc qenv tbool post in
      fmake pre post

    | CI_inv inv ->
      let env, fmake = process_inv tc side in
      let inv = TTC.pf_process_form !!tc env tbool inv in
      subtactic := (fun tc ->
        FApi.t_firsts t_logic_trivial 2 (EcPhlFun.t_fun inv tc));
      fmake inv

    | CI_upto info ->
      let bad, p, q, form = process_upto tc side info in
      let t_tr = FApi.t_or (t_assumption `Conv) t_logic_trivial in
      subtactic := (fun tc ->
        FApi.t_firsts t_tr 3 (EcPhlFun.t_equivF_abs_upto bad p q tc));
      form
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut
      ~prcut:(process_cut tc) tc info
  in

  let t_call tc =
    let env   = FApi.tc1_env  tc in
    let concl = FApi.tc1_goal tc in

    match ax.f_node, concl.f_node with
    | FhoareF hf, FhoareS hs ->
        let (_, f, _), _ = tc1_last_call tc hs.hs_s in
        if not (EcEnv.NormMp.x_equal env hf.hf_f f) then
          tc_error_lazy !!tc (fun fmt ->
            let ppe = EcPrinting.PPEnv.ofenv env in
              Format.fprintf fmt
                "call cannot be used with a lemma referring to `%a': \
                 the last statement is a call to `%a'"
                (EcPrinting.pp_funname ppe) hf.hf_f
                (EcPrinting.pp_funname ppe) f);
        t_hoare_call hf.hf_pr hf.hf_po tc

    | FbdHoareF hf, FbdHoareS hs ->
        let (_, f, _), _ = tc1_last_call tc hs.bhs_s in
        if not (EcEnv.NormMp.x_equal env hf.bhf_f f) then
          tc_error_lazy !!tc (fun fmt ->
            let ppe = EcPrinting.PPEnv.ofenv env in
              Format.fprintf fmt
                "call cannot be used with a lemma referring to `%a': \
                 the last statement is a call to `%a'"
                (EcPrinting.pp_funname ppe) hf.bhf_f
                (EcPrinting.pp_funname ppe) f);
        t_bdhoare_call hf.bhf_pr hf.bhf_po None tc

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
        t_equiv_call ef.ef_pr ef.ef_po tc

    | FbdHoareF hf, FequivS _ ->
        let side =
          match side with
          | None -> tc_error !!tc "side can only be given for prhl judgements"
          | Some side -> side
        in
          t_equiv_call1 side hf.bhf_pr hf.bhf_po tc

    | _, _ -> tc_error !!tc "call: invalid goal shape"

  in
    FApi.t_seqsub
      t_call
      [FApi.t_seq (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt) !subtactic; t_id]
      tc
