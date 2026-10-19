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
(* Procedure calls in the delayed-coupling logic (paper §5).

   Stacks handed over to a procedure (the [T_i] of the call rule and
   the [S_i] of the goal) must only mention global variables: the
   callee cannot observe the caller's locals, so delayed instructions
   that touch caller locals have to be popped before calling.          *)

(* -------------------------------------------------------------------- *)
let pv_of_lv env (lv : lvalue option) =
  match lv with
  | None -> PV.empty
  | Some (LvVar (pv, ty)) -> PV.add env pv ty PV.empty
  | Some (LvTuple pvs) ->
      List.fold_left (fun s (pv, ty) -> PV.add env pv ty s) PV.empty pvs

let fv_of_args env m args =
  PV.fv env m (EcCoreFol.form_of_expr ~m (e_tuple args))

(* Side conditions shared by the call rules, for one side:
     - the arguments are evaluated before the delayed instructions
       [tin] that precede the callee: Write(tin) ⊥ Fv(args);
     - the result assignment commutes with the continuation [tout]:
       x ∉ Read(tout) ∪ Write(tout).                                    *)
let check_call_side_conditions ~who tc env m (lv, _, args) ~tin ~tout =
  if not (PV.indep env (s_write env tin) (fv_of_args env m args)) then
    tc_error !!tc ~who
      "Write(T) and Fv(args) are not disjoint";
  let x = pv_of_lv env lv in
  if not (PV.indep env x (PV.union (s_read env tout) (s_write env tout))) then
    tc_error !!tc ~who
      "the result variable occurs in Read(S) or Write(S)"

(* -------------------------------------------------------------------- *)
(* Call (two-sided).
     Spec   : { φ' | T1 × T2 } F1 ~ F2 { ψ' | S1 × S2 }
     Concl. : { φ  | R1 × R2 } C1; x1 ← F1(a1) ~ C2; x2 ← F2(a2) { ψ | S1 × S2 }
     Premise: { φ  | R1 × R2 } C1 ~ C2
              { φ'[a/params] ∧ ∀ mods res, ψ' ⇒ ψ[x := res] | T1 × T2 }
   The wp of the call is the one of pRHL: ψ and ψ' both talk about the
   memory right after the call, before [S_i] runs.                      *)
let t_dc_call_r ~fpre ~fpost ~tl ~tr tc =
  let who  = "dcoupl call" in
  let env  = FApi.tc1_env tc in
  let hyps = FApi.tc1_hyps tc in
  let es   = tc1_as_dcEquivS tc in
  let ml, mr = fst es.dces_ml, fst es.dces_mr in

  let fpre  = ts_inv_rebind fpre  ml mr in
  let fpost = ts_inv_rebind fpost ml mr in

  let ((_, fl, _) as call_l), cl = tc1_last_call tc es.dces_cl in
  let ((_, fr, _) as call_r), cr = tc1_last_call tc es.dces_cr in

  List.iter (EcPhlDCCore.check_global_stack ~who tc)
    [tl; tr; es.dces_sl; es.dces_sr];
  check_call_side_conditions ~who tc env ml call_l ~tin:tl ~tout:es.dces_sl;
  check_call_side_conditions ~who tc env mr call_r ~tin:tr ~tout:es.dces_sr;

  (* The procedures satisfy their specification *)
  let f_concl = f_dcEquivF fpre tl fl es.dces_sl tr fr es.dces_sr fpost in

  (* The wp. The premise's post is evaluated before [T_i; F_i] runs,
     the goal's post after: generalize over what both modify.          *)
  let mods = (s_write env tl, s_write env tr) in
  let post =
    EcPhlCall.compute_equiv_call_post
      hyps (ml, mr) (fpre.inv, fpost.inv) ~mods call_l call_r (dces_po es).inv in
  let post = { ml; mr; inv = post; } in

  let concl =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr) (dces_pr es)
      es.dces_rl es.dces_rr cl cr post tl tr
  in
  FApi.xmutate1 tc `DCCall [f_concl; concl]

let t_dc_call ~fpre ~fpost ~tl ~tr =
  FApi.t_low0 "dc-call" (t_dc_call_r ~fpre ~fpost ~tl ~tr)

(* -------------------------------------------------------------------- *)
(* Call_L / Call_R (one-sided), with a lossless Hoare specification.
     Spec   : [ F : φ' ==> ψ' ] = 1
     Concl. : { φ | R1 × R2 } C1; x ← F(a) ~ C2 { ψ | R1 × S2 }
     Premise: { φ | R1 × R2 } C1 ~ C2 { φ'[a] ∧ ∀ mods res, ψ' ⇒ ψ[x := res] | R1 × S2 }
   The chosen side's stacks are unchanged by the call (S = R), and the
   call must commute with the delayed instructions:
     Write(R) ⊥ Read(F) ∪ Write(F)    Read(R) ⊥ Write(F)                *)
let t_dc_call1_r ~side ~fpre ~fpost tc =
  let who  = "dcoupl call" in
  let env  = FApi.tc1_env tc in
  let hyps = FApi.tc1_hyps tc in
  let es   = tc1_as_dcEquivS tc in
  let ml, mr = fst es.dces_ml, fst es.dces_mr in
  let me = sideif side ml mr in

  let fpre  = ss_inv_rebind fpre  me in
  let fpost = ss_inv_rebind fpost me in

  let body, r, s =
    sideif side
      (es.dces_cl, es.dces_rl, es.dces_sl)
      (es.dces_cr, es.dces_rr, es.dces_sr) in
  let ((_, f, _) as call), fstmt = tc1_last_call tc body in

  if not (EcReduction.EqTest.for_stmt env r s) then
    tc_error !!tc ~who
      "one-sided call: the continuation must equal the delay context";
  EcPhlDCCore.check_global_stack ~who tc r;
  check_call_side_conditions ~who tc env me call ~tin:r ~tout:s;

  let wr = s_write env r and rr = s_read env r in
  let wf = f_write env f and rf = f_read env f in
  if not (PV.indep env wr (PV.union rf wf)) then
    tc_error !!tc ~who
      "Write(R) and Read(F) ∪ Write(F) are not disjoint";
  if not (PV.indep env rr wf) then
    tc_error !!tc ~who
      "Read(R) and Write(F) are not disjoint";

  (* The procedure satisfies its (lossless) specification *)
  let fconcl =
    f_bdHoareF fpre f fpost FHeq { m = fpost.m; inv = f_r1; } in

  (* The wp *)
  let post =
    EcPhlCall.compute_equiv1_call_post
      hyps side (ml, mr) (fpre.inv, fpost.inv) call (dces_po es).inv in
  let post = { ml; mr; inv = post; } in

  let mtl, mtr = snd es.dces_ml, snd es.dces_mr in
  let concl =
    match side with
    | `Left  ->
        f_dcEquivS mtl mtr (dces_pr es)
          es.dces_rl es.dces_rr fstmt es.dces_cr post es.dces_sl es.dces_sr
    | `Right ->
        f_dcEquivS mtl mtr (dces_pr es)
          es.dces_rl es.dces_rr es.dces_cl fstmt post es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCCall [fconcl; concl]

let t_dc_call1 ~side ~fpre ~fpost =
  FApi.t_low0 "dc-call1" (t_dc_call1_r ~side ~fpre ~fpost)

(* -------------------------------------------------------------------- *)
(* Abs (F-level, abstract procedures / adversaries).
     { I ∧ ={params} ∧ ={glob A} | R1 × R2 } A.f ~ A.f { I ∧ ={res} ∧ ={glob A} | R1 × R2 }
   from, for each oracle O allowed to A,
     { I ∧ ={params} | R1 × R2 } O_l ~ O_r { I ∧ ={res} | R1 × R2 }
   Side conditions (via the module restrictions of A): A cannot access
   the free variables of I, nor Read(R_i) ∪ Write(R_i).                 *)
let t_dc_fun_abs_r (inv : ts_inv) tc =
  let who = "dcoupl proc" in
  let env = FApi.tc1_env tc in
  let ef  = tc1_as_dcEquivF tc in

  if not (EcReduction.EqTest.for_stmt env ef.dcef_rl ef.dcef_sl) then
    tc_error !!tc ~who "left continuation must equal left delay context";
  if not (EcReduction.EqTest.for_stmt env ef.dcef_rr ef.dcef_sr) then
    tc_error !!tc ~who "right continuation must equal right delay context";
  List.iter (EcPhlDCCore.check_global_stack ~who tc) [ef.dcef_rl; ef.dcef_rr];

  let pre, post, sg =
    EcPhlFun.FunAbsLow.equivF_abs_spec !!tc env ef.dcef_fl ef.dcef_fr inv in

  let (topl, _, _, _), (topr, _, _, _) =
    EcLowPhlGoal.abstract_info2 env ef.dcef_fl ef.dcef_fr in
  let rw s = PV.union (s_read env s) (s_write env s) in
  PV.check_depend env (rw ef.dcef_rl) topl;
  PV.check_depend env (rw ef.dcef_rr) topr;

  (* Oracle premises carry the (unchanged) stacks. *)
  let sg =
    List.map (fun g ->
      let o = destr_equivF g in
      f_dcEquivF (ef_pr o)
        ef.dcef_rl o.ef_fl ef.dcef_sl
        ef.dcef_rr o.ef_fr ef.dcef_sr
        (ef_po o)) sg in

  (* Conseq at F-level. *)
  let (mprl, mprr), (mpol, mpor) =
    EcEnv.Fun.equivF_memenv ef.dcef_ml ef.dcef_mr ef.dcef_fl ef.dcef_fr env in
  let pre  = ts_inv_rebind pre  ef.dcef_ml ef.dcef_mr in
  let post = ts_inv_rebind post ef.dcef_ml ef.dcef_mr in
  let cond1 = map_ts_inv2 f_imp (dcef_pr ef) pre in
  let cond2 = map_ts_inv2 f_imp post (dcef_po ef) in
  let concl1 = f_forall_mems_ts_inv mprl mprr cond1 in
  let concl2 = f_forall_mems_ts_inv mpol mpor cond2 in

  FApi.xmutate1 tc `DCFunAbs (concl1 :: concl2 :: sg)

let t_dc_fun_abs inv = FApi.t_low0 "dc-fun-abs" (t_dc_fun_abs_r inv)

(* [proc I] on an F-level dcoupl goal: Abs for abstract procedures,
   plain unfolding otherwise.                                           *)
let t_dc_fun (inv : ts_inv) tc =
  let env = FApi.tc1_env tc in
  let ef  = tc1_as_dcEquivF tc in
  if   NormMp.is_abstract_fun ef.dcef_fl env
  then t_dc_fun_abs inv tc
  else EcPhlDCCore.t_dc_fun_def tc

(* -------------------------------------------------------------------- *)
(* Apply a call rule from an axiom (a lemma or a cut). *)
let call_error env tc f1 f2 =
  tc_error_lazy !!tc (fun fmt ->
      let ppe = EcPrinting.PPEnv.ofenv env in
      Format.fprintf fmt
        "call cannot be used with a lemma referring to `%a': \
         the last statement is a call to `%a'"
        (EcPrinting.pp_funname ppe) f1
        (EcPrinting.pp_funname ppe) f2)

let t_dc_call_ax side ax tc =
  let env = FApi.tc1_env tc in
  let hyps, concl = FApi.tc1_flat tc in
  let ax = EcReduction.h_red_until EcReduction.full_red hyps ax in
  match ax.f_node, concl.f_node with
  | FdcEquivF ef, FdcEquivS es ->
      let (_, fl, _), _ = tc1_last_call tc es.dces_cl in
      let (_, fr, _), _ = tc1_last_call tc es.dces_cr in
      if not (EcEnv.NormMp.x_equal env ef.dcef_fl fl) then
        call_error env tc ef.dcef_fl fl;
      if not (EcEnv.NormMp.x_equal env ef.dcef_fr fr) then
        call_error env tc ef.dcef_fr fr;
      if not (EcReduction.EqTest.for_stmt env ef.dcef_sl es.dces_sl) then
        tc_error !!tc ~who:"dcoupl call"
          "the left continuation of the specification must equal \
           the one of the goal";
      if not (EcReduction.EqTest.for_stmt env ef.dcef_sr es.dces_sr) then
        tc_error !!tc ~who:"dcoupl call"
          "the right continuation of the specification must equal \
           the one of the goal";
      t_dc_call ~fpre:(dcef_pr ef) ~fpost:(dcef_po ef)
        ~tl:ef.dcef_rl ~tr:ef.dcef_rr tc

  | FbdHoareF hf, FdcEquivS es ->
      let side =
        match side with
        | None -> tc_error !!tc "dcoupl call: a side {1|2} should be provided"
        | Some side -> side
      in
      let body = sideif side es.dces_cl es.dces_cr in
      let (_, f, _), _ = tc1_last_call tc body in
      if not (EcEnv.NormMp.x_equal env hf.bhf_f f) then
        call_error env tc hf.bhf_f f;
      t_dc_call1 ~side ~fpre:(bhf_pr hf) ~fpost:(bhf_po hf) tc

  | _, _ -> tc_error !!tc "dcoupl call: invalid goal shape"

(* -------------------------------------------------------------------- *)
(* Specification built from an invariant, for [call (_: I)]. *)
let mk_dc_inv_spec env (inv : ts_inv) fl fr ~tl ~tr ~sl ~sr =
  let ml, mr = inv.ml, inv.mr in
  let pre, post =
    if NormMp.is_abstract_fun fl env then begin
      let (topl, _, _, sigl), (topr, _, _, sigr) =
        EcLowPhlGoal.abstract_info2 env fl fr in
      let eqglob = ts_inv_eqglob topl ml topr mr in
      let eq_params =
        ts_inv_eqparams
          sigl.fs_arg sigl.fs_anames ml
          sigr.fs_arg sigr.fs_anames mr in
      let eq_res = ts_inv_eqres sigl.fs_ret ml sigr.fs_ret mr in
      (map_ts_inv f_ands [eq_params; eqglob; inv],
       map_ts_inv f_ands [eq_res; eqglob; inv])
    end else begin
      let sigl = (EcEnv.Fun.by_xpath fl env).f_sig in
      let sigr = (EcEnv.Fun.by_xpath fr env).f_sig in
      let eq_params =
        ts_inv_eqparams
          sigl.fs_arg sigl.fs_anames ml
          sigr.fs_arg sigr.fs_anames mr in
      let eq_res = ts_inv_eqres sigl.fs_ret ml sigr.fs_ret mr in
      (map_ts_inv2 f_and eq_params inv, map_ts_inv2 f_and eq_res inv)
    end
  in
  f_dcEquivF pre tl fl sl tr fr sr post

(* -------------------------------------------------------------------- *)
let process_dc_fun_abs inv tc =
  let hyps = FApi.tc1_hyps tc in
  let ml, mr = EcIdent.create "&1", EcIdent.create "&2" in
  let env' = LDecl.inv_memenv ml mr hyps in
  let inv  = TTC.pf_process_form !!tc env' tbool inv in
  t_dc_fun { inv; ml; mr; } tc

(* -------------------------------------------------------------------- *)
let process_dc_call side info (ts : (pstmt * pstmt) option) tc =
  let es = tc1_as_dcEquivS tc in

  (* The intermediate stacks [T_i], defaulting to the continuations. *)
  let process_stacks tc =
    match ts with
    | None -> (es.dces_sl, es.dces_sr)
    | Some (ptl, ptr) ->
        let open EcMaps in
        let ml = Mstr.add "r" es.dces_rl.s_node Mstr.empty in
        let ml = Mstr.add "s" es.dces_sl.s_node ml in
        let tl = TTC.tc1_process_prhl_stmt ~map:ml tc `Left  ptl in
        let mr = Mstr.add "r" es.dces_rr.s_node Mstr.empty in
        let mr = Mstr.add "s" es.dces_sr.s_node mr in
        let tr = TTC.tc1_process_prhl_stmt ~map:mr tc `Right ptr in
        (tl, tr)
  in

  let process_spec_2 tc pre post =
    let hyps = FApi.tc1_hyps tc in
    let (_, fl, _) = fst (tc1_last_call tc es.dces_cl) in
    let (_, fr, _) = fst (tc1_last_call tc es.dces_cr) in
    let (ml, mr) = (EcIdent.create "&1", EcIdent.create "&2") in
    let penv, qenv = LDecl.equivF ml mr fl fr hyps in
    let pre  = TTC.pf_process_form !!tc penv tbool pre  in
    let post = TTC.pf_process_form !!tc qenv tbool post in
    let tl, tr = process_stacks tc in
    f_dcEquivF { ml; mr; inv = pre; }
      tl fl es.dces_sl tr fr es.dces_sr
      { ml; mr; inv = post; }
  in

  let process_spec_1 tc side pre post =
    let hyps = FApi.tc1_hyps tc in
    let body = sideif side es.dces_cl es.dces_cr in
    let m = sideif side (EcIdent.create "&1") (EcIdent.create "&2") in
    let (_, f, _) = fst (tc1_last_call tc body) in
    let penv, qenv = LDecl.hoareF m f hyps in
    let pre  = TTC.pf_process_form !!tc penv tbool pre  in
    let post = TTC.pf_process_form !!tc qenv tbool post in
    f_bdHoareF { m; inv = pre; } f { m; inv = post; } FHeq { m; inv = f_r1; }
  in

  let process_inv tc inv =
    let hyps = FApi.tc1_hyps tc in
    let ml, mr = fst es.dces_ml, fst es.dces_mr in
    let (_, fl, _) = fst (tc1_last_call tc es.dces_cl) in
    let (_, fr, _) = fst (tc1_last_call tc es.dces_cr) in
    let mel, mer = EcMemory.abstract ml, EcMemory.abstract mr in
    let hyps = LDecl.push_active_ts mel mer hyps in
    let env  = LDecl.toenv hyps in
    let inv  = TTC.pf_process_form !!tc hyps tbool inv in
    let inv  = { ml; mr; inv; } in
    let tl, tr = process_stacks tc in
    (mk_dc_inv_spec env inv fl fr ~tl ~tr ~sl:es.dces_sl ~sr:es.dces_sr, inv)
  in

  let subtactic = ref t_id in

  let process_cut tc info =
    match info, side with
    | DCI_spec (pre, post), None ->
        process_spec_2 tc pre post
    | DCI_spec (pre, post), Some side ->
        if not (is_none ts) then
          tc_error !!tc "one-sided dcoupl call does not take stacks";
        process_spec_1 tc side pre post
    | DCI_inv _, Some _ ->
        tc_error !!tc "cannot specify side for call with invariants"
    | DCI_inv inv, None ->
        let f, inv = process_inv tc inv in
        subtactic := (fun tc ->
          FApi.t_firsts t_trivial 2 (t_dc_fun inv tc));
        f
  in

  let pt = PT.tc1_process_full_pterm_cut ~prcut:(process_cut tc) tc info in

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
    (t_dc_call_ax side ax)
    [FApi.t_seqs
       [EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt;
        !subtactic; t_trivial];
     t_id]
    tc
