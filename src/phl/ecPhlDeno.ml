(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcTypes
open EcFol
open EcEnv
open EcPV
open EcPhlPrRw
open EcHiGoal
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal
open EcCoreGoal.FApi

module PT  = EcProofTerm
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let real_le_trans     = EcCoreLib.CI_Real.real_order_lemma "ler_trans"
let real_ler_add      = EcCoreLib.CI_Real.real_order_lemma "ler_add"
let real_eq_le        = EcCoreLib.CI_Real.real_order_lemma "lerr_eq"
let real_upto         = EcCoreLib.CI_Real.real_lemma "upto2_abs"
let real_upto_notbad  = EcCoreLib.CI_Real.real_lemma "upto2_notbad"
let real_upto_imp_bad = EcCoreLib.CI_Real.real_lemma "upto2_imp_bad"
let real_upto_false   = EcCoreLib.CI_Real.real_lemma "upto_bad_false"
let real_upto_or      = EcCoreLib.CI_Real.real_lemma "upto_bad_or"
let real_upto_sub     = EcCoreLib.CI_Real.real_lemma "upto_bad_sub"

(* -------------------------------------------------------------------- *)
let t_real_le_trans f2 tc =
  t_apply_prept (`App (`UG real_le_trans, [`F f2]))tc

(* -------------------------------------------------------------------- *)
let t_core_phoare_deno pre post tc =
  let m = pre.m in
  let env, _, concl = FApi.tc1_eflat tc in

  let cmp, f, bd, concl_post =
    match concl.f_node with
    | Fapp ({f_node = Fop (op, _)}, [f; bd])
        when is_pr f && EcPath.p_equal op EcCoreLib.CI_Real.p_real_le ->
      (FHle, f, bd, fun ev po -> map_ss_inv2 f_imp_simpl ev po)

    | Fapp ({f_node = Fop (op, _)}, [bd; f])
        when is_pr f && EcPath.p_equal op EcCoreLib.CI_Real.p_real_le ->
      (FHge, f, bd, fun ev po -> map_ss_inv2 f_imp_simpl po ev)

    | Fapp ({f_node = Fop (op, _)}, [f; bd])
        when is_pr f && EcPath.p_equal op EcCoreLib.CI_Bool.p_eq ->
      (FHeq, f, bd, map_ss_inv2 f_iff_simpl)

    | _ -> tc_error !!tc "invalid goal shape"
  in

  let pr = destr_pr f in
  let concl_e = f_bdHoareF pre pr.pr_fun post cmp {m;inv=bd} in
  let fun_ = EcEnv.Fun.by_xpath pr.pr_fun env in

  (* building the substitution for the pre *)
  let sargs = PVM.add env pv_arg m pr.pr_args PVM.empty in
  let smem = Fsubst.f_bind_mem Fsubst.f_subst_id m pr.pr_mem in
  let concl_pr = Fsubst.f_subst smem ((PVM.subst env sargs) pre.inv) in

  (* building the substitution for the post *)
  let ev = pr.pr_event in
  let me = EcEnv.Fun.actmem_post ev.m fun_ in
  let post = ss_inv_rebind post ev.m in
  let concl_po = EcSubst.f_forall_mems_ss_inv me (concl_post ev post) in

  FApi.xmutate1 tc `HlDeno [concl_e; concl_pr; concl_po]

(* -------------------------------------------------------------------- *)
let t_phoare_deno_r pre post tc =
  let concl = FApi.tc1_goal tc in

  match concl.f_node with
  | Fapp ({f_node = Fop (op, _)}, [f; _bd])
      when EcPath.p_equal op EcCoreLib.CI_Bool.p_eq && not (is_pr f) ->
    (t_symmetry @! t_core_phoare_deno pre post) tc

  | _ -> t_core_phoare_deno pre post tc


(* -------------------------------------------------------------------- *)
let t_ehoare_deno_r pre post tc =
  let m = pre.m in
  assert (m = post.m);
  let env, _, concl = FApi.tc1_eflat tc in

  let f, bd =
    match concl.f_node with
    | Fapp ({f_node = Fop (op, _)}, [f; bd])
        when is_pr f && EcPath.p_equal op EcCoreLib.CI_Real.p_real_le ->
      (f, bd)

    | _ -> tc_error !!tc "invalid goal shape"
  in

  let pr = destr_pr f in
  let concl_e = f_eHoareF pre pr.pr_fun post in
  let _, mpo = EcEnv.Fun.hoareF_memenv m pr.pr_fun env in
  (* pre <= bd *)
  (* building the substitution for the pre *)
  let sargs = PVM.add env pv_arg m pr.pr_args PVM.empty in
  let smem = Fsubst.f_bind_mem Fsubst.f_subst_id m pr.pr_mem in
  let pre = Fsubst.f_subst smem (PVM.subst env sargs pre.inv) in
  let concl_pr = f_xreal_le pre (f_r2xr bd) in

  (* forall m, ev%r%xr <= post *)
  let ev = pr.pr_event in
  let ev = ss_inv_rebind ev m in
  let concl_po = map_ss_inv2 f_xreal_le (map_ss_inv1 f_b2xr ev) post in
  let concl_po = f_forall_mems_ss_inv mpo concl_po in

  FApi.xmutate1 tc `HlDeno [concl_e; concl_pr; concl_po]

(* -------------------------------------------------------------------- *)
let cond_pre env prl prr pre =
  (* building the substitution for the pre *)
  (* we substitute param by args and left by ml and right by mr *)
  let ml, mr = pre.ml, pre.mr in
  let sargs = PVM.add env pv_arg ml prl.pr_args PVM.empty in
  let sargs = PVM.add env pv_arg mr prr.pr_args sargs in
  let smem  = Fsubst.f_subst_id in
  let smem  = Fsubst.f_bind_mem smem ml prl.pr_mem in
  let smem  = Fsubst.f_bind_mem smem mr prr.pr_mem in
  Fsubst.f_subst smem (PVM.subst env sargs pre.inv)

let t_equiv_deno_r pre post tc =
  let env, _, concl = FApi.tc1_eflat tc in
  let ml, mr = pre.ml, pre.mr in

  let cmp, f1, f2 =
    match concl.f_node with
    | Fapp({f_node = Fop(op,_)}, [f1;f2]) when is_pr f1 && is_pr f2 &&
        (EcPath.p_equal op EcCoreLib.CI_Bool.p_eq ||
         EcPath.p_equal op EcCoreLib.CI_Real.p_real_le) ->
      let cmp =
        match op with
        | _ when EcPath.p_equal op EcCoreLib.CI_Bool.p_eq -> `Eq
        | _ when EcPath.p_equal op EcCoreLib.CI_Real.p_real_le -> `Le
        | _ -> assert false
      in cmp, f1, f2

    | _ -> tc_error !!tc "invalid goal shape"

 in

  let (prl, prr) = (destr_pr f1, destr_pr f2) in
  let concl_e = f_equivF pre prl.pr_fun prr.pr_fun post in
  let funl = EcEnv.Fun.by_xpath prl.pr_fun env in
  let funr = EcEnv.Fun.by_xpath prr.pr_fun env in

  (* building the substitution for the pre *)
  (* we substitute param by args and left by ml and right by mr *)
  let concl_pr = cond_pre env prl prr pre in

  (* building the substitution for the post *)
  let evl = ss_inv_generalize_as_left prl.pr_event ml mr in
  let evr = ss_inv_generalize_as_right prr.pr_event ml mr in
  let cmp   =
    match cmp with
    | `Eq -> map_ts_inv2 f_iff evl evr
    | `Le -> map_ts_inv2 f_imp evl evr
    | `Ge -> map_ts_inv2 f_imp evr evl in

  let mel = EcEnv.Fun.actmem_post ml funl in
  let mer = EcEnv.Fun.actmem_post mr funr in
  let concl_po = f_forall_mems_ts_inv mel mer (map_ts_inv2 f_imp post cmp) in

  FApi.xmutate1 tc `HlDeno [concl_e; concl_pr; concl_po]

(* -------------------------------------------------------------------- *)
let t_phoare_deno = FApi.t_low2 "phoare-deno" t_phoare_deno_r
let t_ehoare_deno = FApi.t_low2 "ehoare-deno" t_ehoare_deno_r
let t_equiv_deno  = FApi.t_low2 "equiv-deno"  t_equiv_deno_r

(* -------------------------------------------------------------------- *)
let process_phoare_deno info tc =
  let error () =
    tc_error !!tc "the conclusion is not a suitable Pr expression" in

  let process_cut (pre, post) =
    let hyps, concl = FApi.tc1_flat tc in
    let cmp, f, bd =
      match concl.f_node with
      | Fapp ({f_node = Fop (op, _)}, [f1; f2])
          when EcPath.p_equal op EcCoreLib.CI_Bool.p_eq
        ->
             if is_pr f1 then (FHeq, f1, f2)
        else if is_pr f2 then (FHeq, f2, f1)
        else error ()

      | Fapp({f_node = Fop (op, _)}, [f1; f2])
          when EcPath.p_equal op EcCoreLib.CI_Real.p_real_le
        ->
             if is_pr f1 then (FHle, f1, f2) (* f1 <= f2 *)
        else if is_pr f2 then (FHge, f2, f1) (* f2 >= f1 *)
        else error ()

      | _ -> error ()
    in

    let { pr_fun = f } as pr = destr_pr f in
    let event = pr.pr_event in
    let m = event.m in
    let penv, qenv = LDecl.hoareF m f hyps in
    let pre  = pre  |> omap_dfl (fun p -> TTC.pf_process_formula !!tc penv p) f_true in
    let post = post |> omap_dfl (fun p -> TTC.pf_process_formula !!tc qenv p) event.inv in

    f_bdHoareF {m;inv=pre} f {m;inv=post} cmp {m;inv=bd}
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut
      ~prcut:process_cut tc info in

  let pre, post =
    let bhf = pf_as_bdhoareF !!tc ax in
      (bhf_pr bhf, bhf_po bhf)
  in

  FApi.t_first (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt) (t_phoare_deno pre post tc)

(* -------------------------------------------------------------------- *)
let process_ehoare_deno info tc =
  let error () =
    tc_error !!tc "the conclusion is not a suitable Pr expression" in

  let process_cut (pre, post) =
    let hyps, concl = FApi.tc1_flat tc in
    let f, bd =
      match concl.f_node with
      | Fapp({f_node = Fop (op, _)}, [f1; f2])
          when EcPath.p_equal op EcCoreLib.CI_Real.p_real_le && is_pr f1 ->
          (f1, f2) (* f1 <= f2 *)
      | _ -> error ()
    in

    let { pr_fun = f } as pr = destr_pr f in
    let event = pr.pr_event in
    let m = event.m in
    let penv, qenv = LDecl.hoareF m f hyps in
    let smem = Fsubst.f_bind_mem Fsubst.f_subst_id pr.pr_mem m in
    let dpre = {m;inv=f_r2xr (Fsubst.f_subst smem bd)} in

    let pre  = pre  |> omap_dfl (fun p -> {m;inv=TTC.pf_process_xreal !!tc penv p}) dpre  in
    let post = post |> omap_dfl (fun p -> {m;inv=TTC.pf_process_xreal !!tc qenv p}) (map_ss_inv1 f_b2xr event) in

    f_eHoareF pre f post
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut
      ~prcut:process_cut tc info in

  let pre, post =
    let hf = pf_as_ehoareF !!tc ax in
      (ehf_pr hf, ehf_po hf)
  in

  FApi.t_first (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt) (t_ehoare_deno pre post tc)


(* -------------------------------------------------------------------- *)
let destr_deno_bad env f =
  try
    let fpr1, (fpr2, fpr3) = snd_map DestrReal.add (DestrReal.le f) in
    let _, pr2, pr3 = t3_map destr_pr (fpr1, fpr2, fpr3) in

    if not (NormMp.x_equal env pr2.pr_fun pr3.pr_fun) then
      raise (DestrError "");
    (fpr1, fpr2, fpr3)

  with DestrError _ -> raise (DestrError "destr_deno_bad")

(* -------------------------------------------------------------------- *)
let tc_destr_deno_bad tc env f =
  try  destr_deno_bad env f
  with DestrError _ -> tc_error !!tc "invalid goal shape"

(* -------------------------------------------------------------------- *)
let t_pr_pos tc =
  let pr =
    try
      let _, fpr = DestrReal.le (tc1_goal tc) in
      destr_pr fpr
    with DestrError _ -> tc_error !!tc "invalid goal shape" in
  let prf = f_pr_r {pr with pr_event = {m=pr.pr_event.m; inv=f_false}} in
  (t_real_le_trans prf @+
    [ t_pr_rewrite ("mu_false", None) @! t_true;
      t_pr_rewrite ("mu_sub", None) @! t_true]) tc

(* -------------------------------------------------------------------- *)
let t_equiv_deno_bad pre tc =
  let env, _hyps, concl = FApi.tc1_eflat tc in
  let fpr1, fpr2, fprb = tc_destr_deno_bad tc env concl in
  let pr1 = destr_pr fpr1 and pr2 = destr_pr fpr2 and prb = destr_pr fprb in
  let m = prb.pr_event.m in
  let ev2 = ss_inv_rebind pr2.pr_event m in
  let fand = map_ss_inv2 f_and ev2 (map_ss_inv1 f_not prb.pr_event) in
  let pro = f_pr pr2.pr_mem pr2.pr_fun pr2.pr_args (map_ss_inv2 f_or fand prb.pr_event) in
  let pra = f_pr pr2.pr_mem pr2.pr_fun pr2.pr_args fand in
  let t_false tc = t_apply_prept (`UG real_upto_false) tc in
  let ml, mr = pre.ml, pre.mr in
  let post =
    let ev1 = ss_inv_generalize_as_left pr1.pr_event ml mr in
    let ev2 = ss_inv_generalize_as_right ev2 ml mr in
    let bad2 = ss_inv_generalize_as_right prb.pr_event ml mr in
    map_ts_inv2 f_imp (map_ts_inv1 f_not bad2) (map_ts_inv2 f_imp ev1 ev2) in

  (t_real_le_trans pro @+
     [t_equiv_deno pre post @+ [
       t_id;
       t_id;
       t_intros_s (`Symbol ["_";"_"]) @! t_apply_prept (`UG real_upto_or) ];
      t_pr_rewrite_i ("mu_disjoint", None) @+
       [ t_intro_s (`Symbol "_") @! t_false;
         t_apply_prept
           (`App (`UG real_ler_add, [`F pra;`F fpr2;`F fprb;`F fprb; `H_; `H_]))
           @+ [
             t_pr_rewrite_i ("mu_sub",None) @+ [
               t_intros_s (`Symbol ["_"]) @! t_apply_prept (`UG real_upto_sub);
               t_trivial;
             ];
             t_true;
           ]
       ]
     ]) tc

(* -------------------------------------------------------------------- *)
let destr_deno_bad2 env f =
  try
    let lhs , rhs  = DestrReal.le f in
    let fpr1, fpr2 = DestrReal.sub (DestrReal.abs lhs) in
    let _pr1, pr2, prb = t3_map destr_pr (fpr1, fpr2, rhs) in
      if not (NormMp.x_equal env pr2.pr_fun prb.pr_fun) then
        raise (DestrError "pr");
      (fpr1, fpr2, rhs)
  with DestrError _ -> raise (DestrError "destr_deno_bad2")

(* -------------------------------------------------------------------- *)
let tc_destr_deno_bad2 tc env f =
  try  destr_deno_bad2 env f
  with DestrError _ -> tc_error !!tc "invalid goal shape"

(* -------------------------------------------------------------------- *)
let t_equiv_deno_bad2 pre bad1 tc =
  let ml, mr = pre.ml, pre.mr in
  let env, hyps, concl = FApi.tc1_eflat tc in
  let fpr1, fpr2, fprb = tc_destr_deno_bad2 tc env concl in
  let pr1 = destr_pr fpr1 and pr2 = destr_pr fpr2 and
      prb = destr_pr fprb in
  let f1 = pr1.pr_fun and f2 = pr2.pr_fun in
  let ev1 = pr1.pr_event and ev2 = pr2.pr_event in
  let ev1 = ss_inv_rebind ev1 bad1.m in
  let bad2 = prb.pr_event in
  let bad2 = ss_inv_rebind bad2 ev2.m in
  let post =
    let bad1 = ss_inv_generalize_as_left bad1 ml mr in
    let ev1 = ss_inv_generalize_as_left ev1 ml mr in
    let bad2 = ss_inv_generalize_as_right bad2 ml mr in
    let ev2 = ss_inv_generalize_as_right ev2 ml mr in
    map_ts_inv2 f_and (map_ts_inv2 f_iff bad1 bad2)
      (map_ts_inv2 f_imp (map_ts_inv1 f_not bad2) (map_ts_inv2 f_iff ev1 ev2)) in
  let equiv = f_equivF pre f1 f2 post in
  let cpre = cond_pre env pr1 pr2 pre in
  let fpreb1 = f_pr pr1.pr_mem pr1.pr_fun pr1.pr_args (map_ss_inv2 f_and ev1 bad1) in
  let fpren1 = f_pr pr1.pr_mem pr1.pr_fun pr1.pr_args (map_ss_inv2 f_and ev1 (map_ss_inv1 f_not bad1)) in
  let fpreb2 = f_pr pr1.pr_mem pr2.pr_fun pr2.pr_args (map_ss_inv2 f_and ev2 bad2) in
  let fpren2 = f_pr pr1.pr_mem pr2.pr_fun pr2.pr_args (map_ss_inv2 f_and ev2 (map_ss_inv1 f_not bad2)) in
  let fabs' =
    f_real_abs
      (f_real_sub (f_real_add fpreb1 fpren1) (f_real_add fpreb2 fpren2)) in
  let hequiv,hcpre = as_seq2 (EcEnv.LDecl.fresh_ids hyps ["_";"_"]) in
  (t_cut equiv @+
    [ t_id;
      t_cut cpre @+
        [ t_id;
          t_intros_i [hcpre; hequiv] @!
            t_real_le_trans fabs' @+
            [ t_apply_prept (`UG real_eq_le) @!
                process_congr @! (* abs *)
                process_congr @~ (* add *)
                (t_last process_congr) @~+ (* opp *)
                [ t_pr_rewrite_i ("mu_split", Some bad1) @! t_reflex;
                  t_pr_rewrite_i ("mu_split", Some bad2) @! t_reflex ] ;
              t_apply_prept (`UG real_upto) @+
                [ t_pr_pos;
                  t_pr_pos;
                  t_equiv_deno pre post @+ [
                    t_apply_hyp hequiv;
                    t_apply_hyp hcpre;
                    t_intros_s (`Symbol ["_"; "_"]) @!
                      t_apply_prept (`UG real_upto_imp_bad) ];
                  t_pr_rewrite ("mu_sub",None) @! t_trivial;
                  t_equiv_deno pre post @+ [
                    t_apply_hyp hequiv;
                    t_apply_hyp hcpre;
                    t_intros_s (`Symbol ["_"; "_"]) @!
                    t_apply_prept (`UG real_upto_notbad)
                  ];
                ]
            ]
        ]
    ]) tc

(* -------------------------------------------------------------------- *)
let process_pre tc hyps prl prr pre post =
  let fl = prl.pr_fun and fr = prr.pr_fun in
  let ml, mr = post.ml, post.mr in
  match pre with
  | Some p ->
    let penv, _ = LDecl.equivF ml mr fl fr hyps in
    {ml;mr;inv=TTC.pf_process_formula !!tc penv p}
  | None ->
    let al = prl.pr_args and ar = prr.pr_args in
    let pml = prl.pr_mem and pmr = prr.pr_mem in

    let env = LDecl.toenv hyps in
    let eqs = ref [] in
    let push f = eqs := f :: !eqs in

    let dopv m mi gen_o x ty =
      if is_glob x then push (gen_o (map_ss_inv1 (fun f -> f_eq f (f_pvar x ty mi).inv) (f_pvar x ty m))) in

    let doglob m mi gen_o g = push (gen_o ((map_ss_inv1 (fun f -> f_eq f (NormMp.norm_glob env mi g).inv)) (NormMp.norm_glob env m g))) in
    let dof f a m mi gen_o =
      try
        let fv = PV.remove env pv_res (PV.fv env m post.inv) in
        PV.iter (dopv m mi gen_o) (doglob m mi gen_o) (eqobs_inF_refl env f fv);
        if not (EcReduction.EqTest.for_type env a.f_ty tunit) then
          push (map_ts_inv1 (fun f -> f_eq f a) (gen_o (f_pvarg a.f_ty m)))
      with EcCoreGoal.TcError _ | EqObsInError -> () in

    let gen_r f = ss_inv_generalize_right f mr in
    let gen_l f = ss_inv_generalize_left  f ml in
    dof fl al ml pml gen_r; dof fr ar mr pmr gen_l;
    map_ts_inv ~ml ~mr f_ands !eqs

(* -------------------------------------------------------------------- *)
let post_iff ml mr eq env evl evr =
  let post = map_ts_inv2 f_iff evl evr in
  try
    if not eq then raise Not_found;
    {ml;mr;inv=Mpv2.to_form
      (Mpv2.needed_eq env post) ml mr f_true}
  with Not_found -> post

(* -------------------------------------------------------------------- *)
let process_equiv_deno1 info eq tc =
  let process_cut (pre, post) =
    let env, hyps, concl = FApi.tc1_eflat tc in

    let op, f1, f2 =
      match concl.f_node with
      | Fapp ({f_node = Fop (op, _)}, [f1; f2]) when is_pr f1 && is_pr f2 ->
          (op, f1, f2)

      | _ -> tc_error !!tc "invalid goal shape"
    in

    let ml , mr = EcIdent.create "&1", EcIdent.create "&2" in

    let { pr_fun = fl } as prl = destr_pr f1 in
    let evl = ss_inv_generalize_as_left prl.pr_event ml mr in
    let { pr_fun = fr } as prr = destr_pr f2 in
    let evr = ss_inv_generalize_as_right prr.pr_event ml mr in

    let post =
      match post with
      | Some p ->
        let _, qenv = LDecl.equivF ml mr fl fr hyps in
        {ml;mr;inv=TTC.pf_process_formula !!tc qenv p}
      | None ->
        match op with
        | _ when EcPath.p_equal op EcCoreLib.CI_Bool.p_eq ->
           (post_iff ml mr eq env evl evr)
        | _ when EcPath.p_equal op EcCoreLib.CI_Real.p_real_le ->
           map_ts_inv2 f_imp evl evr
        | _ ->
           tc_error !!tc "not able to reconize a comparison operator" in

    let pre = process_pre tc hyps prl prr pre post in

    f_equivF pre fl fr post
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut
      ~prcut:process_cut tc info in

  let pre, post =
    let ef = pf_as_equivF !!tc ax in
      (ef_pr ef, ef_po ef)
  in

  FApi.t_first (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt) (t_equiv_deno pre post tc)

(* -------------------------------------------------------------------- *)
let process_equiv_deno_bad info tc =
  let process_cut (pre, post) =
    let env, hyps, concl = FApi.tc1_eflat tc in
    let fpr1, fpr2, fprb = tc_destr_deno_bad tc env concl in

    let { pr_fun = fl ; pr_event = evl } as prl = destr_pr fpr1 in
    let { pr_fun = fr ; pr_event = evr } as prr = destr_pr fpr2 in

    let ml , mr = EcIdent.create "&1", EcIdent.create "&2" in

    let post =
      match post with
      | Some p ->
        let _, qenv = LDecl.equivF ml mr fl fr hyps in
        {ml;mr;inv=TTC.pf_process_formula !!tc qenv p}
      | None ->
        let evl = ss_inv_generalize_as_left evl ml mr in
        let evr = ss_inv_generalize_as_right evr ml mr in
        let bad = ss_inv_generalize_as_right (destr_pr fprb).pr_event ml mr in
        let f_imps' l = f_imps (List.tl l) (List.hd l) in
        map_ts_inv f_imps' [evr; map_ts_inv1 f_not bad; evl] in
    let pre = process_pre tc hyps prl prr pre post in

    f_equivF pre fl fr post
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut
      ~prcut:process_cut tc info in

  let equiv = pf_as_equivF !!tc ax in
  let pre = (ef_pr equiv) in

  let torotate = ref 1 in
  let t_sub =
    FApi.t_or (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt)
      (EcPhlConseq.t_equivF_conseq pre (ef_po equiv) @+
         [t_true; (fun tc -> incr torotate;t_id tc);
          EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt]) in
  let gs =
    t_last t_sub (t_rotate `Left 1 (t_equiv_deno_bad pre tc)) in
  t_rotate `Left !torotate gs

(* -------------------------------------------------------------------- *)
let process_equiv_deno info eq g =
  let env, _hyps, concl = FApi.tc1_eflat g in
  try ignore (destr_deno_bad env concl);
      process_equiv_deno_bad info g
  with DestrError _ ->
    process_equiv_deno1 info eq g

(* -------------------------------------------------------------------- *)
let process_equiv_deno_bad2 info eq bad1 tc =
  let env, hyps, concl = FApi.tc1_eflat tc in
  let fpr1, fpr2, fprb = tc_destr_deno_bad2 tc env concl in

  let { pr_fun = fl; pr_mem = ml ; pr_event = evl } as prl = destr_pr fpr1 in
  let { pr_fun = fr; pr_event = evr } as prr = destr_pr fpr2 in

  let ml' , mr' = EcIdent.create "&1", EcIdent.create "&2" in

  let bad1 =
    let _, qenv = LDecl.hoareF ml fl hyps in
    {m=ml;inv=TTC.pf_process_formula !!tc qenv bad1} in

  let process_cut (pre, post) =

    let post =
      match post with
      | Some p ->
        let _, qenv = LDecl.equivF ml' mr' fl fr hyps in
        {ml=ml';mr=mr';inv=TTC.pf_process_formula !!tc qenv p}
      | None ->
        let evl = ss_inv_generalize_as_left evl ml' mr' in
        let evr = ss_inv_generalize_as_right evr ml' mr' in
        let bad1 = ss_inv_generalize_as_left bad1 ml' mr' in
        let bad2 = ss_inv_generalize_as_right (destr_pr fprb).pr_event ml' mr' in
        let iff = post_iff ml' mr' eq env evl evr in
        map_ts_inv2 f_and (map_ts_inv2 f_iff bad1 bad2) (map_ts_inv2 f_imp (map_ts_inv1 f_not bad2) iff) in

    let pre = process_pre tc hyps prl prr pre post in

    f_equivF pre fl fr post
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut
      ~prcut:process_cut tc info in

  let equiv = pf_as_equivF !!tc ax in
  let pre = (ef_pr equiv) in

  let torotate = ref 1 in
  let t_sub =
    FApi.t_or (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt)
      (EcPhlConseq.t_equivF_conseq pre (ef_po equiv) @+
         [t_true; (fun tc -> incr torotate;t_id tc);
          EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt]) in
  let gs =
    t_last t_sub (t_rotate `Left 1 (t_equiv_deno_bad2 pre bad1 tc)) in
  t_rotate `Left !torotate gs

(* -------------------------------------------------------------------- *)
type denoff = deno_ppterm * bool * pformula option

let process_deno mode (info, eq, bad1) g =
  match mode with
  | `PHoare -> process_phoare_deno info g
  | `EHoare -> process_ehoare_deno info g
  | `Equiv  ->
    match bad1 with
    | None -> process_equiv_deno info eq g
    | Some bad1 -> process_equiv_deno_bad2 info eq bad1 g
