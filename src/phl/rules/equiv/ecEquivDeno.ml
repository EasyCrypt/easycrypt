(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcTypes
open EcFol
open EcEnv
open EcPV
open EcHiGoal
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal
open EcCoreGoal.FApi

module PT  = EcProofTerm
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameters of the equiv [deno] rule: the pre- and postcondition of the
   judgement on the two procedures, in one pair of memories. Already
   typed, nothing to resolve: the same record is the rule argument and the
   node payload. *)
type equiv_deno = {
  eqd_pre  : ts_inv;    (* P *)
  eqd_post : ts_inv;    (* Q *)
}

type EcCoreGoal.rule += REquivDeno of equiv_deno

(* -------------------------------------------------------------------- *)
(* The goals the rule applies to: [Pr[...] = Pr[...]] and
   [Pr[...] <= Pr[...]]. *)
let destr_deno_goal (concl : form) =
  match concl.f_node with
  | Fapp ({f_node = Fop (op, _)}, [f1; f2]) when is_pr f1 && is_pr f2 ->
         if EcPath.p_equal op EcCoreLib.CI_Bool.p_eq      then Some (`Eq, destr_pr f1, destr_pr f2)
    else if EcPath.p_equal op EcCoreLib.CI_Real.p_real_le then Some (`Le, destr_pr f1, destr_pr f2)
    else None

  | _ -> None

(* [P] and [Q] share their two memories, which are distinct and do not
   occur free in the goal (they are bound around the events of the goal in
   the third premise). *)
let valid_memories (concl : form) (n : equiv_deno) =
  let { ml; mr } = n.eqd_pre in
     EcIdent.id_equal ml n.eqd_post.ml
  && EcIdent.id_equal mr n.eqd_post.mr
  && not (EcIdent.id_equal ml mr)
  && not (EcIdent.Mid.mem ml concl.f_fv)
  && not (EcIdent.Mid.mem mr concl.f_fv)

(* -------------------------------------------------------------------- *)
(* [P], with the arguments and the initial memories of [prl] and [prr]. *)
let cond_pre env prl prr pre =
  let ml, mr = pre.ml, pre.mr in
  let sargs = PVM.add env pv_arg ml prl.pr_args PVM.empty in
  let sargs = PVM.add env pv_arg mr prr.pr_args sargs in
  let smem  = Fsubst.f_subst_id in
  let smem  = Fsubst.f_bind_mem smem ml prl.pr_mem in
  let smem  = Fsubst.f_bind_mem smem mr prr.pr_mem in
  Fsubst.f_subst smem (PVM.subst env sargs pre.inv)

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   shape of the goal and the memories of [P] and [Q]) are part of it, so
   the checker re-validates them. *)
let equiv_deno_subgoals (hyps : LDecl.hyps) (concl : form) (n : equiv_deno) =
  let env = LDecl.toenv hyps in
  let cmp, prl, prr =
    match destr_deno_goal concl with
    | Some x -> x
    | None   -> failwith "equiv-deno: invalid goal shape" in
  if not (valid_memories concl n) then
    failwith "equiv-deno: invalid memories";
  let ml, mr = n.eqd_pre.ml, n.eqd_pre.mr in
  let concl_e = f_equivF n.eqd_pre prl.pr_fun prr.pr_fun n.eqd_post in
  let funl = Fun.by_xpath prl.pr_fun env in
  let funr = Fun.by_xpath prr.pr_fun env in

  let concl_pr = cond_pre env prl prr n.eqd_pre in

  (* Q relates the two events, in every pair of final memories *)
  let evl = ss_inv_generalize_as_left  prl.pr_event ml mr in
  let evr = ss_inv_generalize_as_right prr.pr_event ml mr in
  let cmp =
    match cmp with
    | `Eq -> map_ts_inv2 f_iff evl evr
    | `Le -> map_ts_inv2 f_imp evl evr in
  let mel = Fun.actmem_post ml funl in
  let mer = Fun.actmem_post mr funr in
  let concl_po =
    f_forall_mems_ts_inv mel mer (map_ts_inv2 f_imp n.eqd_post cmp) in

  [concl_e; concl_pr; concl_po]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_equiv_deno (r : equiv_deno) (tc : tcenv1) =
  let concl = FApi.tc1_goal tc in
  if Option.is_none (destr_deno_goal concl) then
    tc_error !!tc "invalid goal shape";
  if not (valid_memories concl r) then
    tc_error !!tc "invalid memories for the equivalence judgement";
  FApi.xrule1 tc (REquivDeno r)
    (equiv_deno_subgoals (FApi.tc1_hyps tc) concl r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivDeno n ->
         Some (EcPlRecheck.checker_of "equiv-deno" (fun _ concl -> concl)
                 (fun hyps concl -> equiv_deno_subgoals hyps concl n))
     | _ -> None)

(* ==================================================================== *)
(* Derived (no proof-node): the upto-bad forms, from the rule and the
   lemmas of [Real] on probabilities, the probability rewritings being
   [rewrite Pr] ([EcBdHoarePrFact]). *)
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
  t_apply_prept (`App (`UG real_le_trans, [`F f2])) tc

(* -------------------------------------------------------------------- *)
(* [Pr[f1 @ &1 : E1] <= Pr[f2 @ &2 : E2] + Pr[f2 @ &2 : B]], [f2] the
   same procedure in the last two probabilities. *)
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
(* [0%r <= Pr[...]] *)
let t_pr_pos tc =
  let pr =
    try
      let _, fpr = DestrReal.le (tc1_goal tc) in
      destr_pr fpr
    with DestrError _ -> tc_error !!tc "invalid goal shape" in
  let prf = f_pr_r { pr with pr_event = { m = pr.pr_event.m; inv = f_false; }; } in
  (t_real_le_trans prf @+
    [ EcBdHoarePrFact.t_pr_rewrite ("mu_false", None) @! t_true;
      EcBdHoarePrFact.t_pr_rewrite ("mu_sub", None) @! t_true]) tc

(* -------------------------------------------------------------------- *)
let t_equiv_deno_bad pre tc =
  let env, _hyps, concl = FApi.tc1_eflat tc in
  let fpr1, fpr2, fprb = tc_destr_deno_bad tc env concl in
  let pr1 = destr_pr fpr1 and pr2 = destr_pr fpr2 and prb = destr_pr fprb in
  if not (pr2.pr_mem = prb.pr_mem) then
    tc_error !!tc "invalid goal shape";
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
     [t_equiv_deno { eqd_pre = pre; eqd_post = post; } @+ [
       t_id;
       t_id;
       t_intros_s (`Symbol ["_";"_"]) @! t_apply_prept (`UG real_upto_or) ];
      EcBdHoarePrFact.t_pr_rewrite ("mu_disjoint", None) @+
       [ t_intro_s (`Symbol "_") @! t_false;
         t_apply_prept
           (`App (`UG real_ler_add, [`F pra;`F fpr2;`F fprb;`F fprb; `H_; `H_]))
           @+ [
             EcBdHoarePrFact.t_pr_rewrite ("mu_sub",None) @+ [
               t_intros_s (`Symbol ["_"]) @! t_apply_prept (`UG real_upto_sub);
               t_trivial;
             ];
             t_true;
           ]
       ]
     ]) tc

(* -------------------------------------------------------------------- *)
(* [`|Pr[f1 @ &1 : E1] - Pr[f2 @ &2 : E2]| <= Pr[f2 @ &2 : B]], [f2] the
   same procedure in the last two probabilities. *)
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
  if not (pr2.pr_mem = prb.pr_mem) then
    tc_error !!tc "invalid goal shape";
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
  let fpreb2 = f_pr pr2.pr_mem pr2.pr_fun pr2.pr_args (map_ss_inv2 f_and ev2 bad2) in
  let fpren2 = f_pr pr2.pr_mem pr2.pr_fun pr2.pr_args (map_ss_inv2 f_and ev2 (map_ss_inv1 f_not bad2)) in
  let fabs' =
    f_real_abs
      (f_real_sub (f_real_add fpreb1 fpren1) (f_real_add fpreb2 fpren2)) in
  let t_deno = t_equiv_deno { eqd_pre = pre; eqd_post = post; } in
  let hequiv,hcpre = as_seq2 (EcEnv.LDecl.fresh_ids hyps ["_";"_"]) in
  (t_cut equiv @+
    [ t_id;
      t_cut cpre @+
        [ t_id;
          t_intros_i [hcpre; hequiv] @!
            t_real_le_trans fabs' @+
            [ t_apply_prept (`UG real_eq_le) @!
                (process_congr PCongrDefault) @! (* abs *)
                (process_congr PCongrDefault) @~ (* add *)
                (t_last (process_congr PCongrDefault)) @~+ (* opp *)
                [ EcBdHoarePrFact.t_pr_rewrite ("mu_split", Some bad1) @! t_reflex;
                  EcBdHoarePrFact.t_pr_rewrite ("mu_split", Some bad2) @! t_reflex ] ;
              t_apply_prept (`UG real_upto) @+
                [ t_pr_pos;
                  t_pr_pos;
                  t_deno @+ [
                    t_apply_hyp hequiv;
                    t_apply_hyp hcpre;
                    t_intros_s (`Symbol ["_"; "_"]) @!
                      t_apply_prept (`UG real_upto_imp_bad) ];
                  EcBdHoarePrFact.t_pr_rewrite ("mu_sub",None) @! t_trivial;
                  t_deno @+ [
                    t_apply_hyp hequiv;
                    t_apply_hyp hcpre;
                    t_intros_s (`Symbol ["_"; "_"]) @!
                    t_apply_prept (`UG real_upto_notbad)
                  ];
                ]
            ]
        ]
    ]) tc

(* ==================================================================== *)
(* Elaboration. *)

(* The default precondition: the equalities of the globals read by the two
   procedures (for the variables the postcondition reads) and of their
   arguments with those of the goal. *)
let process_pre tc hyps prl prr pre post =
  let fl = prl.pr_fun and fr = prr.pr_fun in
  let ml, mr = post.ml, post.mr in
  match pre with
  | Some p ->
    let penv, _ = LDecl.equivF ml mr fl fr hyps in
    { ml; mr; inv = TTC.pf_process_formula !!tc penv p; }
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
(* The default postcondition of an equality: [E1 <=> E2], or the
   equalities of the variables it needs when [eq]. *)
let post_iff ml mr eq env evl evr =
  let post = map_ts_inv2 f_iff evl evr in
  try
    if not eq then raise Not_found;
    { ml; mr; inv = Mpv2.to_form (Mpv2.needed_eq env post) ml mr f_true; }
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
        { ml; mr; inv = TTC.pf_process_formula !!tc qenv p; }
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

  let ef = pf_as_equivF !!tc ax in

  FApi.t_first
    (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt)
    (t_equiv_deno { eqd_pre = ef_pr ef; eqd_post = ef_po ef; } tc)

(* -------------------------------------------------------------------- *)
(* The judgement is applied, or used through the consequence rule when it
   does not match; the goals are rotated so that those of the judgement
   come first.

   TEMPORARY: the consequence rule still comes from the not-yet-migrated
   [EcPhlConseq]. *)
let t_deno_bad_sub pt (equiv : equivF) (t_bad : backward) (tc : tcenv1) =
  let torotate = ref 1 in
  let t_sub =
    FApi.t_or (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt)
      (EcPhlConseq.t_equivF_conseq (ef_pr equiv) (ef_po equiv) @+
         [t_true; (fun tc -> incr torotate; t_id tc);
          EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt]) in
  let gs = t_last t_sub (t_rotate `Left 1 (t_bad tc)) in
  t_rotate `Left !torotate gs

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
        { ml; mr; inv = TTC.pf_process_formula !!tc qenv p; }
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

  t_deno_bad_sub pt equiv (t_equiv_deno_bad (ef_pr equiv)) tc

(* -------------------------------------------------------------------- *)
let process_equiv_deno_bad2 info eq bad1 tc =
  let env, hyps, concl = FApi.tc1_eflat tc in
  let fpr1, fpr2, fprb = tc_destr_deno_bad2 tc env concl in

  let { pr_fun = fl; pr_mem = ml ; pr_event = evl } as prl = destr_pr fpr1 in
  let { pr_fun = fr; pr_event = evr } as prr = destr_pr fpr2 in

  let ml' , mr' = EcIdent.create "&1", EcIdent.create "&2" in

  let bad1 =
    let _, qenv = LDecl.hoareF ml fl hyps in
    { m = ml; inv = TTC.pf_process_formula !!tc qenv bad1; } in

  let process_cut (pre, post) =

    let post =
      match post with
      | Some p ->
        let _, qenv = LDecl.equivF ml' mr' fl fr hyps in
        { ml = ml'; mr = mr'; inv = TTC.pf_process_formula !!tc qenv p; }
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

  t_deno_bad_sub pt equiv (t_equiv_deno_bad2 (ef_pr equiv) bad1) tc

(* -------------------------------------------------------------------- *)
let process_equiv_deno ((info, eq, bad1) : deno_ppterm * bool * pformula option) tc =
  match bad1 with
  | Some bad1 ->
      process_equiv_deno_bad2 info eq bad1 tc

  | None ->
      let env, _hyps, concl = FApi.tc1_eflat tc in
      try ignore (destr_deno_bad env concl);
          process_equiv_deno_bad info tc
      with DestrError _ ->
        process_equiv_deno1 info eq tc
