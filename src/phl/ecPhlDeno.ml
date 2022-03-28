(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcEnv
open EcPV
open EcPhlPrRw
open EcHiGoal

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal
open EcCoreGoal.FApi

module PT  = EcProofTerm
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let real_lemma name =
  EcPath.pqname EcCoreLib.CI_Real.p_RealExtra name

let real_order_lemma name =
  EcPath.pqname EcCoreLib.CI_Real.p_RealOrder name

let real_le_trans     = real_order_lemma "ler_trans"
let real_ler_add      = real_order_lemma "ler_add"
let real_eq_le        = real_order_lemma "lerr_eq"
let real_upto         = real_lemma "upto2_abs"
let real_upto_notbad  = real_lemma "upto2_notbad"
let real_upto_imp_bad = real_lemma "upto2_imp_bad"
let real_upto_false   = real_lemma "upto_bad_false"
let real_upto_or      = real_lemma "upto_bad_or"
let real_upto_sub     = real_lemma "upto_bad_sub"

(* -------------------------------------------------------------------- *)
let t_real_le_trans f2 tc =
  t_apply_prept (`App (`UG real_le_trans, [`F f2]))tc

(* -------------------------------------------------------------------- *)
let t_core_phoare_deno pre post tc =
  let env, _, concl = FApi.tc1_eflat tc in

  let cmp, f, bd, concl_post =
    match concl.f_node with
    | Fapp ({f_node = Fop (op, _)}, [f; bd])
        when is_pr f && EcPath.p_equal op EcCoreLib.CI_Real.p_real_le ->
      (FHle, f, bd, fun ev -> f_imp_simpl ev post)

    | Fapp ({f_node = Fop (op, _)}, [bd; f])
        when is_pr f && EcPath.p_equal op EcCoreLib.CI_Real.p_real_le ->
      (FHge, f, bd, fun ev -> f_imp_simpl post ev)

    | Fapp ({f_node = Fop (op, _)}, [f; bd])
        when is_pr f && EcPath.p_equal op EcCoreLib.CI_Bool.p_eq ->
      (FHeq, f, bd, f_iff_simpl post)

    | _ -> tc_error !!tc "invalid goal shape"
  in

  let pr = destr_pr f in
  let concl_e = f_bdHoareF pre pr.pr_fun post cmp bd in
  let fun_ = EcEnv.Fun.by_xpath pr.pr_fun env in

  (* building the substitution for the pre *)
  let sargs = PVM.add env pv_arg mhr pr.pr_args PVM.empty in
  let smem = Fsubst.f_bind_mem Fsubst.f_subst_id mhr pr.pr_mem in
  let concl_pr = Fsubst.f_subst smem (PVM.subst env sargs pre) in

  (* building the substitution for the post *)
  (* FIXME:
   * let smem_ = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mhr in
   * let ev   = Fsubst.f_subst smem_ ev in *)
  let me = EcEnv.Fun.actmem_post mhr fun_ in
  let concl_po = f_forall_mems [me] (concl_post pr.pr_event) in

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
let cond_pre env prl prr pre =
  (* building the substitution for the pre *)
  (* we substitute param by args and left by ml and right by mr *)
  let sargs = PVM.add env pv_arg mleft  prl.pr_args PVM.empty in
  let sargs = PVM.add env pv_arg mright prr.pr_args sargs in
  let smem  = Fsubst.f_subst_id in
  let smem  = Fsubst.f_bind_mem smem mleft  prl.pr_mem in
  let smem  = Fsubst.f_bind_mem smem mright prr.pr_mem in
  Fsubst.f_subst smem (PVM.subst env sargs pre)

let t_equiv_deno_r pre post tc =
  let env, _, concl = FApi.tc1_eflat tc in

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
  let smeml = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mleft in
  let smemr = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mright in
  let evl   = Fsubst.f_subst smeml prl.pr_event in
  let evr   = Fsubst.f_subst smemr prr.pr_event in
  let cmp   =
    match cmp with
    | `Eq -> f_iff evl evr
    | `Le -> f_imp evl evr
    | `Ge -> f_imp evr evl in

  let mel = EcEnv.Fun.actmem_post mleft  funl in
  let mer = EcEnv.Fun.actmem_post mright funr in
  let concl_po = f_forall_mems [mel; mer] (f_imp post cmp) in

  FApi.xmutate1 tc `HlDeno [concl_e; concl_pr; concl_po]

(* -------------------------------------------------------------------- *)
let t_phoare_deno = FApi.t_low2 "phoare-deno" t_phoare_deno_r
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

    let { pr_fun = f; pr_event = event; } = destr_pr f in
    let penv, qenv = LDecl.hoareF f hyps in
    let pre  = pre  |> omap_dfl (fun p -> TTC.pf_process_formula !!tc penv p) f_true in
    let post = post |> omap_dfl (fun p -> TTC.pf_process_formula !!tc qenv p) event in

    f_bdHoareF pre f post cmp bd
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut
      ~prcut:process_cut tc info in

  let pre, post =
    let bhf = pf_as_bdhoareF !!tc ax in
      (bhf.bhf_pr, bhf.bhf_po)
  in

  FApi.t_first (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt) (t_phoare_deno pre post tc)

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
  let prf = f_pr_r {pr with pr_event = f_false} in
  (t_real_le_trans prf @+
    [ t_pr_rewrite ("mu_false", None) @! t_true;
      t_pr_rewrite ("mu_sub", None) @! t_true]) tc

(* -------------------------------------------------------------------- *)
let t_equiv_deno_bad pre tc =
  let env, _hyps, concl = FApi.tc1_eflat tc in
  let fpr1, fpr2, fprb = tc_destr_deno_bad tc env concl in
  let pr1 = destr_pr fpr1 and pr2 = destr_pr fpr2 and prb = destr_pr fprb in
  let fand = f_and pr2.pr_event (f_not prb.pr_event) in
  let pro = f_pr_r { pr2 with pr_event = f_or fand prb.pr_event } in
  let pra = f_pr_r { pr2 with pr_event = fand } in
  let t_false tc = t_apply_prept (`UG real_upto_false) tc in

  let post =
    let subst_l = Fsubst.f_subst_mem mhr mleft in
    let subst_r = Fsubst.f_subst_mem mhr mright in
    let ev1 = subst_l pr1.pr_event in
    let ev2 = subst_r pr2.pr_event in
    let bad2 = subst_r prb.pr_event in
    f_imp (f_not bad2) (f_imp ev1 ev2) in

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
  let env, hyps, concl = FApi.tc1_eflat tc in
  let fpr1, fpr2, fprb = tc_destr_deno_bad2 tc env concl in
  let pr1 = destr_pr fpr1 and pr2 = destr_pr fpr2 and
      prb = destr_pr fprb in
  let f1 = pr1.pr_fun and f2 = pr2.pr_fun in
  let ev1 = pr1.pr_event and ev2 = pr2.pr_event in
  let bad2 = prb.pr_event in
  let post =
    let subst_l = Fsubst.f_subst_mem mhr mleft in
    let subst_r = Fsubst.f_subst_mem mhr mright in
    let bad2 = subst_r bad2 in
    f_and (f_iff (subst_l bad1) bad2)
      (f_imp (f_not bad2) (f_iff (subst_l ev1) (subst_r ev2))) in
  let equiv = f_equivF pre f1 f2 post in
  let cpre = cond_pre env pr1 pr2 pre in
  let fpreb1 = f_pr_r {pr1 with pr_event = f_and ev1 bad1} in
  let fpren1 = f_pr_r {pr1 with pr_event = f_and ev1 (f_not bad1) } in
  let fpreb2 = f_pr_r {pr2 with pr_event = f_and ev2 bad2} in
  let fpren2 = f_pr_r {pr2 with pr_event = f_and ev2 (f_not bad2) } in
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
  match pre with
  | Some p ->
    let penv, _ = LDecl.equivF fl fr hyps in
    TTC.pf_process_formula !!tc penv p
  | None ->
    let al = prl.pr_args and ar = prr.pr_args in
    let ml = prl.pr_mem and mr = prr.pr_mem in
    let env = LDecl.toenv hyps in
    let eqs = ref [] in
    let push f = eqs := f :: !eqs in

    let dopv m mi x ty =
      if is_glob x then push (f_eq (f_pvar x ty m) (f_pvar x ty mi)) in

    let doglob m mi g = push (f_eq (f_glob g m) (f_glob g mi)) in
    let dof f a m mi =
      try
        let fv = PV.remove env pv_res (PV.fv env m post) in
        PV.iter (dopv m mi) (doglob m mi) (eqobs_inF_refl env f fv);
        if not (EcReduction.EqTest.for_type env a.f_ty tunit) then
          push (f_eq (f_pvarg a.f_ty m) a)
      with EcCoreGoal.TcError _ | EqObsInError -> () in

    dof fl al mleft ml; dof fr ar mright mr;
    f_ands !eqs

(* -------------------------------------------------------------------- *)
let post_iff eq env evl evr =
  let post = f_iff evl evr in
  try
    if not eq then raise Not_found;
    Mpv2.to_form mleft mright
      (Mpv2.needed_eq env mleft mright post) f_true
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

    let { pr_fun = fl; pr_event = evl } as prl = destr_pr f1 in
    let { pr_fun = fr; pr_event = evr } as prr = destr_pr f2 in

    let post =
      match post with
      | Some p ->
        let _, qenv = LDecl.equivF fl fr hyps in
        TTC.pf_process_formula !!tc qenv p
      | None ->
        let evl = Fsubst.f_subst_mem mhr mleft evl in
        let evr = Fsubst.f_subst_mem mhr mright evr in
        match op with
        | _ when EcPath.p_equal op EcCoreLib.CI_Bool.p_eq ->
           post_iff eq env evl evr
        | _ when EcPath.p_equal op EcCoreLib.CI_Real.p_real_le ->
           f_imp evl evr
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
      (ef.ef_pr, ef.ef_po)
  in

  FApi.t_first (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt) (t_equiv_deno pre post tc)

(* -------------------------------------------------------------------- *)
let process_equiv_deno_bad info tc =
  let process_cut (pre, post) =
    let env, hyps, concl = FApi.tc1_eflat tc in
    let fpr1, fpr2, fprb = tc_destr_deno_bad tc env concl in

    let { pr_fun = fl; pr_event = evl } as prl = destr_pr fpr1 in
    let { pr_fun = fr; pr_event = evr } as prr = destr_pr fpr2 in

    let post =
      match post with
      | Some p ->
        let _, qenv = LDecl.equivF fl fr hyps in
        TTC.pf_process_formula !!tc qenv p
      | None ->
        let evl = Fsubst.f_subst_mem mhr mleft evl in
        let evr = Fsubst.f_subst_mem mhr mright evr in
        let bad = (destr_pr fprb).pr_event in
        let bad = Fsubst.f_subst_mem mhr mright bad in
        f_imps [f_not bad;evl] evr in
    let pre = process_pre tc hyps prl prr pre post in

    f_equivF pre fl fr post
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut
      ~prcut:process_cut tc info in

  let equiv = pf_as_equivF !!tc ax in
  let pre = equiv.ef_pr in

  let torotate = ref 1 in
  let t_sub =
    FApi.t_or (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt)
      (EcPhlConseq.t_equivF_conseq pre equiv.ef_po @+
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

  let { pr_fun = fl; pr_event = evl } as prl = destr_pr fpr1 in
  let { pr_fun = fr; pr_event = evr } as prr = destr_pr fpr2 in

  let bad1 =
    let _, qenv = LDecl.hoareF fl hyps in
    TTC.pf_process_formula !!tc qenv bad1 in

  let process_cut (pre, post) =

    let post =
      match post with
      | Some p ->
        let _, qenv = LDecl.equivF fl fr hyps in
        TTC.pf_process_formula !!tc qenv p
      | None ->
        let evl = Fsubst.f_subst_mem mhr mleft evl in
        let evr = Fsubst.f_subst_mem mhr mright evr in
        let bad1 = Fsubst.f_subst_mem mhr mleft bad1 in
        let bad2 = (destr_pr fprb).pr_event in
        let bad2 = Fsubst.f_subst_mem mhr mright bad2 in
        let iff = post_iff eq env evl evr in
        f_and (f_iff bad1 bad2) (f_imp (f_not bad2) iff) in

    let pre = process_pre tc hyps prl prr pre post in

    f_equivF pre fl fr post
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut
      ~prcut:process_cut tc info in

  let equiv = pf_as_equivF !!tc ax in
  let pre = equiv.ef_pr in

  let torotate = ref 1 in
  let t_sub =
    FApi.t_or (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt)
      (EcPhlConseq.t_equivF_conseq pre equiv.ef_po @+
         [t_true; (fun tc -> incr torotate;t_id tc);
          EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt]) in
  let gs =
    t_last t_sub (t_rotate `Left 1 (t_equiv_deno_bad2 pre bad1 tc)) in
  t_rotate `Left !torotate gs

(* -------------------------------------------------------------------- *)
type denoff = ((pformula option) tuple2) gppterm * bool * pformula option

let process_deno mode (info, eq, bad1) g =
  match mode with
  | `PHoare -> process_phoare_deno info g
  | `Equiv  ->
    match bad1 with
    | None -> process_equiv_deno info eq g
    | Some bad1 -> process_equiv_deno_bad2 info eq bad1 g
