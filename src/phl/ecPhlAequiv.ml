(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcTypes
open EcFol
open EcCoreGoal
open EcLowPhlGoal

module Mid = EcIdent.Mid
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
module IAPRHL : sig
  val loaded : EcEnv.env -> bool
  val sumr_p : EcPath.path
  val sumr   : form -> form -> form
end = struct
  let p_Aprhl = EcCoreLib.CI_Aprhl.p_Aprhl

  let sumr_p = EcPath.pqname p_Aprhl "sumr"

  let sumr =
    let bgty = [tint; tfun tint treal] in
    let bg   = f_op sumr_p [] (toarrow bgty treal) in
    fun n f -> f_app bg [n; f] treal

  let loaded (env : EcEnv.env) =
    is_some (EcEnv.Theory.by_path_opt p_Aprhl env)
end

(* -------------------------------------------------------------------- *)
(* An [ahoare] post is a single formula: refuse hoare goals carrying
   exceptional postconditions. *)
let plain_hoare_post (pe : proofenv) (po : hs_inv) =
  if not (POE.is_empty po.hsi_inv) then
    tc_error pe "exceptional postconditions are not supported in aprhl";
  { m = po.hsi_m; inv = po.hsi_inv.main }

(* -------------------------------------------------------------------- *)
let t_tohoare_r (tc : tcenv1) =
  match f_node (FApi.tc1_goal tc) with
  | FahoareF ahf ->
     let concl = f_hoareF (ahf_pr ahf) ahf.ahf_f (empty_hs (ahf_po ahf)) in
     let bp = f_real_le f_r0 (ahf_b ahf).inv in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToHoare [bp; concl])
       EcLowGoal.t_trivial tc

  | FahoareS ahs ->
     let concl =
       f_hoareS (snd ahs.ahs_m) (ahs_pr ahs) ahs.ahs_s (empty_hs (ahs_po ahs)) in
     let bp = f_real_le f_r0 (ahs_b ahs).inv in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToHoare [bp; concl])
       EcLowGoal.t_trivial tc

  | _ -> tc_error_noXhl ~kinds:[`AHoare `Any] !!tc

(* -------------------------------------------------------------------- *)
let t_ofhoare_r (tc : tcenv1) =
  match f_node (FApi.tc1_goal tc) with
  | FhoareF hf ->
     let po = plain_hoare_post !!tc (hf_po hf) in
     let concl =
       f_ahoareF ~b:{m = hf.hf_m; inv = f_r0} (hf_pr hf) hf.hf_f po in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToHoare [concl])
       EcLowGoal.t_trivial tc

  | FhoareS hs ->
     let po = plain_hoare_post !!tc (hs_po hs) in
     let concl =
       f_ahoareS (snd hs.hs_m) ~b:{m = fst hs.hs_m; inv = f_r0}
         (hs_pr hs) hs.hs_s po in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToHoare [concl])
       EcLowGoal.t_trivial tc

  | _ -> tc_error_noXhl ~kinds:[`AHoare `Any] !!tc

(* -------------------------------------------------------------------- *)
let t_tohoare = FApi.t_low0 "to-hoare" t_tohoare_r
let t_ofhoare = FApi.t_low0 "of-hoare" t_ofhoare_r

(* -------------------------------------------------------------------- *)
let t_toequiv_r (tc : tcenv1) =
  match f_node (FApi.tc1_goal tc) with
  | FaequivF aef ->
     let concl = f_equivF (aef_pr aef) aef.aef_fl aef.aef_fr (aef_po aef) in
     let ep = f_real_le f_r0 (aef_ep aef).inv in
     let dp = f_real_le f_r0 (aef_dp aef).inv in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToEquiv [ep; dp; concl])
       EcLowGoal.t_trivial tc

  | FaequivS aes ->
     let concl =
       f_equivS (snd aes.aes_ml) (snd aes.aes_mr)
         (aes_pr aes) aes.aes_sl aes.aes_sr (aes_po aes) in
     let ep = f_real_le f_r0 (aes_ep aes).inv in
     let dp = f_real_le f_r0 (aes_dp aes).inv in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToEquiv [ep; dp; concl])
       EcLowGoal.t_trivial tc

  | _ -> tc_error_noXhl ~kinds:[`AEquiv `Any] !!tc

(* -------------------------------------------------------------------- *)
let t_ofequiv_r (tc : tcenv1) =
  match f_node (FApi.tc1_goal tc) with
  | FequivF ef ->
     let ml, mr = ef.ef_ml, ef.ef_mr in
     let r0 = {ml; mr; inv = f_r0} in
     let concl =
       f_aequivF ~ep:r0 ~dp:r0 (ef_pr ef) ef.ef_fl ef.ef_fr (ef_po ef) in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToEquiv [concl])
       EcLowGoal.t_trivial tc

  | FequivS es ->
     let ml, mr = fst es.es_ml, fst es.es_mr in
     let r0 = {ml; mr; inv = f_r0} in
     let concl =
       f_aequivS (snd es.es_ml) (snd es.es_mr) ~ep:r0 ~dp:r0
         (es_pr es) es.es_sl es.es_sr (es_po es) in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToEquiv [concl])
       EcLowGoal.t_trivial tc

  | _ -> tc_error_noXhl ~kinds:[`AEquiv `Any] !!tc

(* -------------------------------------------------------------------- *)
let t_toequiv = FApi.t_low0 "to-equiv" t_toequiv_r
let t_ofequiv = FApi.t_low0 "of-equiv" t_ofequiv_r

(* -------------------------------------------------------------------- *)
let t_lap_r (mode : lap_mode) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let aes = tc1_as_aequivS tc in
  let ml, mr = fst aes.aes_ml, fst aes.aes_mr in
  (* Only used for expressions without program variables. *)
  let mhr = EcIdent.create "&hr" in

  let (x1, ty1), (e1, a1) = tc1_instr_lap tc aes.aes_sl in
  let (x2, ty2), (e2, a2) = tc1_instr_lap tc aes.aes_sr in

  match mode with
  | `Gen (k, k') -> begin
      let k   = TTC.tc1_process_form tc tint k in
      let k'  = TTC.tc1_process_form tc tint k' in
      let rd1 = EcPV.e_read_r env EcPV.PV.empty a1 in
      let rd2 = EcPV.e_read_r env EcPV.PV.empty a2 in

      if EcPV.PV.mem_pv env x1 rd1 || EcPV.PV.mem_pv env x2 rd2 then
        tc_error !!tc "lvalue of rnd-lap cannot occur in the lap argument";

      let f1 = form_of_expr ~m:ml a1 in
      let f2 = form_of_expr ~m:mr a2 in

      let f_lap1 = f_int_le (f_int_abs (f_int_add k (f_int_sub f1 f2))) k'
      and f_lap2 =
        f_eq
          (f_int_add (f_pvar x1 ty1 ml).inv k)
          (f_pvar x2 ty2 mr).inv
      in

      let eqe    = f_eq (form_of_expr ~m:mhr e1) (form_of_expr ~m:mhr e2) in
      let ep     =
        f_real_le
          (f_real_mul (f_real_of_int k') (form_of_expr ~m:mhr e1))
          (aes_ep aes).inv in
      let dp     = f_real_le f_r0 (aes_dp aes).inv in
      let k'ge0  = f_int_le f_i0 k' in
      let concl1 = f_imp (aes_pr aes).inv f_lap1 in
      let concl2 = f_imp (f_and (aes_pr aes).inv f_lap2) (aes_po aes).inv in

      let concl1 = f_forall_mems [aes.aes_ml; aes.aes_mr] concl1 in
      let concl2 = f_forall_mems [aes.aes_ml; aes.aes_mr] concl2 in

      FApi.t_seq
        (fun tc -> FApi.xmutate1 tc `Lap
          [eqe; ep; dp; k'ge0; concl1; concl2])
        EcLowGoal.t_trivial tc
    end

  | `Int (((p, q), (r, s)), (n, sg), k) ->
      let p   = TTC.tc1_process_aprhl_form tc tint p  in
      let q   = TTC.tc1_process_aprhl_form tc tint q  in
      let r   = TTC.tc1_process_aprhl_form tc tint r  in
      let s   = TTC.tc1_process_aprhl_form tc tint s  in
      let en  = TTC.tc1_process_exp tc `InProc (Some tint ) n  in
      let esg = TTC.tc1_process_exp tc `InProc (Some treal) sg in
      let ek  = TTC.tc1_process_exp tc `InProc (Some tint ) k  in
      let rd1 = EcPV.e_read_r env EcPV.PV.empty a1 in
      let rd2 = EcPV.e_read_r env EcPV.PV.empty a2 in

      if EcPV.PV.mem_pv env x1 rd1 || EcPV.PV.mem_pv env x2 rd2 then
        tc_error !!tc "lvalue of rnd-lap cannot occur in the lap argument";

      List.iter (fun z ->
        let rd1 = EcPV.PV.fv (FApi.tc1_env tc) ml z in
        let rd2 = EcPV.PV.fv (FApi.tc1_env tc) mr z in
        if EcPV.PV.mem_pv env x1 rd1 || EcPV.PV.mem_pv env x2 rd2 then
          tc_error !!tc "lvalue of rnd-lap cannot occur in bounds")
      [p; q; r; s];

      let f1 = form_of_expr ~m:ml a1 in
      let f2 = form_of_expr ~m:mr a2 in

      let fx1 = (f_pvar x1 ty1 ml).inv in
      let fx2 = (f_pvar x2 ty2 mr).inv in

      let n  = form_of_expr ~m:mhr en  in
      let sg = form_of_expr ~m:mhr esg in
      let k  = form_of_expr ~m:mhr ek  in

      let pre = f_ands [
        f_int_le (f_int_abs (f_int_sub f1 f2)) k;
        f_int_le (f_int_add p k) r;
        f_int_lt r s;
        f_int_le s (f_int_sub q k);
        f_int_le (f_int_sub (f_int_sub q p) (f_int_sub s r)) n;
        f_real_lt f_r0 sg;
        f_real_le sg (f_real_add
            (f_real_sub (f_real_of_int s) (f_real_of_int r))
            (f_rint (EcBigInt.of_int 2)));
      ]

      and post =
        f_iff
          (f_and (f_int_le p fx1) (f_int_le fx1 q))
          (f_and (f_int_le r fx2) (f_int_le fx2 s))
      in

      let fe1 = form_of_expr ~m:mhr e1 in
      let fe2 = form_of_expr ~m:mhr e2 in

      let eps' = f_real_ln (f_real_div
        (f_real_exp (f_real_mul (f_real_of_int n) fe1))
        (f_real_sub f_r1
           (f_real_exp
             (f_real_div
                (f_real_opp (f_real_mul sg fe1))
                (f_rint (EcBigInt.of_int 2))))))
      in

      let eqe    = f_eq fe1 fe2 in
      let eqeps  = f_eq (aes_ep aes).inv eps' in
      let kge0   = f_int_le f_i0 k in
      let dp     = f_real_le f_r0 (aes_dp aes).inv in
      let ep     = f_real_le f_r0 (aes_ep aes).inv in
      let concl1 = f_imp (aes_pr aes).inv pre in
      let concl2 = f_imp post (aes_po aes).inv in

      FApi.t_seq
        (fun tc -> FApi.xmutate1 tc `Lap
          [dp; ep; kge0; eqe; eqeps;
           f_forall_mems [aes.aes_ml; aes.aes_mr] concl1;
           f_forall_mems [aes.aes_ml; aes.aes_mr] concl2])
        EcLowGoal.t_trivial tc

  | _ -> assert false

(* -------------------------------------------------------------------- *)
let t_lap = FApi.t_low1 "lap" t_lap_r

(* -------------------------------------------------------------------- *)
let t_while_r ((ef, df), (v, inv), nf) tc =
  if not (IAPRHL.loaded (FApi.tc1_env tc)) then
    tacuerror "awhile: load the `Aprhl' theory first";

  let hyps, _ = FApi.tc1_flat tc in
  let aes = tc1_as_aequivS tc in
  let ml, mr = fst aes.aes_ml, fst aes.aes_mr in
  let mhr = EcIdent.create "&hr" in

  let (b1, s1) = tc1_instr_while tc aes.aes_sl in
  let (b2, s2) = tc1_instr_while tc aes.aes_sr in

  let fb1 = form_of_expr ~m:ml b1 in
  let fb2 = form_of_expr ~m:mr b2 in

  let tb = tfun tint treal in
  let ef = TTC.process_exp hyps `InOp (Some tb) ef in
  let df = TTC.process_exp hyps `InOp (Some tb) df in

  let n   = TTC.process_exp hyps `InOp (Some tint) nf in
  let fn  = form_of_expr ~m:mhr n in
  let eff = form_of_expr ~m:mhr ef in
  let dff = form_of_expr ~m:mhr df in

  let v =
    let hyps = EcEnv.LDecl.push_active_ss aes.aes_ml hyps in
    TTC.pf_process_form !!tc hyps tint v
  in

  let inv =
    let hyps = EcEnv.LDecl.push_active_ts aes.aes_ml aes.aes_mr hyps in
    TTC.pf_process_formula !!tc hyps inv
  in

  let k  = EcIdent.create "k" in
  let ki = f_local k tint in

  let ef_gt0 =
    f_forall [k, GTty tint] (f_real_le f_r0 (f_app eff [ki] treal)) in

  let df_gt0 =
    f_forall [k, GTty tint] (f_real_le f_r0 (f_app dff [ki] treal)) in

  let fn_gt0 = f_int_le f_i0 fn in

  let term =
    f_forall_mems [aes.aes_ml; aes.aes_mr]
       (f_imp (f_and inv (f_int_lt v f_i0)) (f_not fb1)) in

  let sub =
    let sub_pre  = f_ands [inv; fb1; fb2; f_eq ki v; f_int_le v fn] in
    let sub_post = f_ands [inv; f_eq fb1 fb2; f_int_lt v ki] in

    f_forall [k, GTty tint] (
      f_aequivS (snd aes.aes_ml) (snd aes.aes_mr)
        ~ep:{ml; mr; inv = form_of_expr ~m:mhr (e_app ef [e_local k tint] treal)}
        ~dp:{ml; mr; inv = form_of_expr ~m:mhr (e_app df [e_local k tint] treal)}
        {ml; mr; inv = sub_pre} s1 s2 {ml; mr; inv = sub_post})
  in

  let concl1 = f_forall_mems [aes.aes_ml; aes.aes_mr]
    (f_imp (aes_pr aes).inv (
       f_ands [inv; f_eq fb1 fb2; f_int_lt v fn])) in

  let concl2 = f_forall_mems [aes.aes_ml; aes.aes_mr]
    (f_imp (f_ands [inv; f_not fb1; f_not fb2]) (aes_po aes).inv) in

  let sume, sumd =
    (f_eq (aes_ep aes).inv (IAPRHL.sumr fn eff),
     f_eq (aes_dp aes).inv (IAPRHL.sumr fn dff))
  in

  FApi.t_seqs [ (fun tc ->
    FApi.t_onselect (fun i -> i = 5 || i = 6)
      (EcLowGoal.t_simplify_with_info
        { EcReduction.no_red with
            EcReduction.delta_p = (fun p ->
              if EcPath.p_equal p IAPRHL.sumr_p then `Force else `No) })
      (FApi.xmutate1 tc `AWhile
         [fn_gt0; ef_gt0; df_gt0; term; concl1; concl2; sume; sumd; sub]));
    EcLowGoal.t_simplify_with_info EcReduction.nodelta;
    EcLowGoal.t_trivial
  ] tc

(* -------------------------------------------------------------------- *)
let t_while = FApi.t_low1 "awhile" t_while_r

(* -------------------------------------------------------------------- *)
let t_while_ac_r ((e, d), (v, inv), (bN, w)) tc =
  if not (IAPRHL.loaded (FApi.tc1_env tc)) then
    tacuerror "awhile: load the `Aprhl' theory first";

  let hyps, _ = FApi.tc1_flat tc in
  let aes = tc1_as_aequivS tc in
  let ml, mr = fst aes.aes_ml, fst aes.aes_mr in
  let mhr = EcIdent.create "&hr" in

  let (b1, s1) = tc1_instr_while tc aes.aes_sl in
  let (b2, s2) = tc1_instr_while tc aes.aes_sr in

  let fb1 = form_of_expr ~m:ml b1 in
  let fb2 = form_of_expr ~m:mr b2 in

  let v =
    let hyps = EcEnv.LDecl.push_active_ss aes.aes_ml hyps in
    TTC.pf_process_form !!tc hyps tint v
  in

  let inv =
    let hyps = EcEnv.LDecl.push_active_ts aes.aes_ml aes.aes_mr hyps in
    TTC.pf_process_formula !!tc hyps inv
  in

  let e  = TTC.process_exp hyps `InOp (Some treal) e  in
  let d  = TTC.process_exp hyps `InOp (Some treal) d  in
  let w  = TTC.process_exp hyps `InOp (Some treal) w  in
  let bN = TTC.process_exp hyps `InOp (Some tint ) bN in

  let ef  = form_of_expr ~m:mhr e  in
  let df  = form_of_expr ~m:mhr d  in
  let wf  = form_of_expr ~m:mhr w  in
  let bNf = form_of_expr ~m:mhr bN in

  let bNr = f_real_of_int bNf   in

  let cond1 = f_forall_mems [aes.aes_ml; aes.aes_mr]
    (f_imps [inv; f_int_le v f_i0] (f_not fb1)) in

  let gt0_w = f_real_lt f_r0 wf in
  let ge0_N = f_int_le  f_i0 bNf in
  let ge0_e = f_real_le f_r0 ef in
  let ge0_d = f_real_le f_r0 df in

  (* Conseq on the bound by hand ... *)
  let eqe =
    let term1 = f_rint (EcBigInt.of_int 2) in
    let term1 = f_real_mul term1 bNr in
    let term1 = f_real_mul term1 (f_real_ln (f_real_inv wf)) in
    let term1 = f_real_mul (f_real_sqrt term1) ef in

    let term2 = f_real_sub (f_real_exp ef) f_r1 in
    let term2 = f_real_mul (f_real_mul bNr ef) term2 in

    f_real_le (f_real_add term1 term2) (aes_ep aes).inv
  in

  let eqd =
    f_real_le (f_real_add (f_real_mul bNr df) wf) (aes_dp aes).inv in

  let concl1 =
    let k  = EcIdent.create "k" in
    let kf = f_local k tint in

    let pre  = f_ands [inv; fb1; fb2; f_eq v kf] in
    let post = f_ands [inv; f_eq fb1 fb2; f_int_lt v kf] in

    let eqv =
      f_aequivS (snd aes.aes_ml) (snd aes.aes_mr)
        ~ep:{ml; mr; inv = ef} ~dp:{ml; mr; inv = df}
        {ml; mr; inv = pre} s1 s2 {ml; mr; inv = post} in

    f_forall [(k, GTty tint)] eqv
  in

  let cond2 =
    f_forall_mems [aes.aes_ml; aes.aes_mr]
    (f_imp (aes_pr aes).inv (f_ands [gt0_w; ge0_N; ge0_e; ge0_d])) in

  let pre  = f_ands [inv; f_eq fb1 fb2; f_int_le v bNf] in
  let post = f_ands [inv; f_not fb1; f_not fb2] in

  FApi.t_last (
     fun tc -> FApi.xmutate1 tc `AWhileAc
       [eqe; eqd; cond1; cond2; concl1])
  (EcPhlConseq.t_aequivS_conseq
     {ml; mr; inv = pre} {ml; mr; inv = post} tc)

(* -------------------------------------------------------------------- *)
let t_while_ac = FApi.t_low1 "awhile-ac" t_while_ac_r

(* -------------------------------------------------------------------- *)
let t_pweq_r (e1, e2) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let aes  = tc1_as_aequivS tc in
  let ml, mr = fst aes.aes_ml, fst aes.aes_mr in

  let e1 =
    let hyps = EcEnv.LDecl.push_active_ss aes.aes_ml hyps in
    TTC.pf_process_form_opt !!tc hyps None e1

  and e2 =
    let hyps = EcEnv.LDecl.push_active_ss aes.aes_mr hyps in
    TTC.pf_process_form_opt !!tc hyps None e2
  in

  if not (EcReduction.EqTest.for_type (FApi.tc1_env tc) e1.f_ty e2.f_ty) then
    tc_error !!tc "pweq: incompatible type for expr.";

  let ll1   = f_losslessS aes.aes_ml aes.aes_sl in
  let ll2   = f_losslessS aes.aes_mr aes.aes_sr in
  let eq0   = f_eq (aes_dp aes).inv f_r0 in

  let concl, conseq =
    let nmx  = EcIdent.create "x" in
    let varx = f_local nmx e1.f_ty in

    let post  = f_imp (f_eq varx e1) (f_eq varx e2) in
    let concl =
      f_forall [nmx, GTty varx.f_ty]
        (f_aequivS (snd aes.aes_ml) (snd aes.aes_mr)
           ~ep:(aes_ep aes) ~dp:{ml; mr; inv = f_r0}
           (aes_pr aes) aes.aes_sl aes.aes_sr {ml; mr; inv = post})
    and conseq =
      f_forall_mems [aes.aes_ml; aes.aes_mr]
        (f_imp (f_forall [nmx, GTty varx.f_ty] post) (aes_po aes).inv)
    in (concl, conseq)
  in

  FApi.t_seqs [
    (fun tc -> FApi.xmutate1 tc `APwEq
       [ll1; ll2; eq0; conseq; concl]);
    EcLowGoal.t_simplify_with_info EcReduction.nodelta;
    EcLowGoal.t_trivial
  ] tc

(* -------------------------------------------------------------------- *)
let t_pweq = FApi.t_low1 "pweq" t_pweq_r

(* -------------------------------------------------------------------- *)
let t_bw_r ((f, g), (p, q)) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let env  = FApi.tc1_env  tc in
  let aes  = tc1_as_aequivS tc in
  let ml, mr = fst aes.aes_ml, fst aes.aes_mr in
  let mhr = EcIdent.create "&hr" in

  let (x1, ty1), mu1 = tc1_instr_rnd1 tc aes.aes_sl in
  let (x2, ty2), mu2 = tc1_instr_rnd1 tc aes.aes_sr in

  if not (EcReduction.EqTest.for_type env mu1.e_ty mu2.e_ty) then
    tc_error !!tc "left and right distribution must have the same domain";

  let muty   = proj_distr_ty env mu1.e_ty in
  let bijty  = tfun muty muty in
  let predty = tfun muty tbool in

  let f = TTC.pf_process_exp !!tc hyps `InProc (Some bijty) f in
  let g = TTC.pf_process_exp !!tc hyps `InProc (Some bijty) g in

  let opf arg = f_app (form_of_expr ~m:mhr f) [arg] muty in
  let opg arg = f_app (form_of_expr ~m:mhr g) [arg] muty in

  let p = TTC.pf_process_form !!tc hyps predty p in
  let q = TTC.pf_process_form !!tc hyps predty q in

  let pdp arg = f_app p [arg] tbool in
  let pdq arg = f_app q [arg] tbool in

  let px1 = (f_pvar x1 ty1 ml).inv in
  let px2 = (f_pvar x2 ty2 mr).inv in

  let d_ge0 = f_real_le f_r0 (aes_dp aes).inv in

  let invx =
    let x   = EcIdent.create "x" in
    let pvx = f_local x muty in
    f_forall [x, GTty muty] (f_imp (pdp pvx)
      (f_and (pdq (opf pvx)) (f_eq (opg (opf pvx)) pvx)))
   in

  let invy =
    let y   = EcIdent.create "y" in
    let pvy = f_local y muty in
    f_forall [y, GTty muty] (f_imp (pdq pvy)
      (f_and (pdp (opg pvy)) (f_eq (opf (opg pvy)) pvy)))
   in

  let aequivS_dp0 pr po =
    f_aequivS (snd aes.aes_ml) (snd aes.aes_mr)
      ~ep:(aes_ep aes) ~dp:{ml; mr; inv = f_r0}
      {ml; mr; inv = pr} aes.aes_sl aes.aes_sr {ml; mr; inv = po} in

  let concl1 =
    let v    = EcIdent.create "v" in
    let pvv  = f_local v muty in
    let post = f_imp (f_eq pvv px1) (f_eq pvv px2) in
    f_forall [v, GTty muty]
      (f_imp (f_not (pdp pvv)) (aequivS_dp0 f_true post))
  in

  let concl2 =
    let v    = EcIdent.create "v" in
    let pvv  = f_local v muty in
    let post = f_imp (f_eq pvv px1) (f_eq pvv (opf px2)) in
    f_forall [v, GTty muty]
      (f_imp (pdp pvv) (aequivS_dp0 f_true post))
  in

  let po = f_imp (pdp px1) (pdq px2) in

  FApi.t_last (
    FApi.t_seqs [
      (fun tc -> FApi.xmutate1 tc `ABw
         [d_ge0; invx; invy; concl1; concl2]);
      EcLowGoal.t_simplify_with_info EcReduction.nodelta;
      EcLowGoal.t_trivial
    ])
  (EcPhlConseq.t_aequivS_conseq
     {ml; mr; inv = f_true} {ml; mr; inv = po} tc)

(* -------------------------------------------------------------------- *)
let t_bw = FApi.t_low1 "bw" t_bw_r

(* -------------------------------------------------------------------- *)
let t_utb_l_r ((e1, e2), (bad, delta)) tc =
  let hyps = FApi.tc1_hyps tc in
  let aes  = tc1_as_aequivS tc in
  let ml, mr = fst aes.aes_ml, fst aes.aes_mr in

  let e1, bad =
    let hyps = EcEnv.LDecl.push_active_ss aes.aes_ml hyps in
    (TTC.pf_process_form_opt !!tc hyps None e1,
     TTC.pf_process_formula  !!tc hyps bad) in

  let e2 =
    let hyps = EcEnv.LDecl.push_active_ss aes.aes_mr hyps in
    TTC.pf_process_form_opt !!tc hyps (Some e1.f_ty) e2
  in

  let delta =
    TTC.pf_process_form_opt !!tc hyps (Some treal) delta in

  let eq_e = f_eq e1 e2 in
  (* 1: post => e1 = e2, application of conseq *)
  let cond_c =
    f_forall_mems [aes.aes_ml; aes.aes_mr]
      (f_imp (aes_po aes).inv eq_e) in
  (* first condition, bounding bad *)
  let cond_d =
    let m     = EcIdent.create "&hr" in
    let subst = Fsubst.f_subst_mem ml m in
    let pre   = subst (aes_pr aes).inv in
    let post  = subst bad in
    let concl =
      f_bdHoareS (snd aes.aes_ml)
        {m; inv = pre} aes.aes_sl {m; inv = post} FHle {m; inv = delta} in
    f_forall_mems [aes.aes_mr] concl in
  (* FIXME: check 0 <= aes_dp - delta *)
  let cond_a =
    let post = f_imp (f_not bad) eq_e in
    f_aequivS (snd aes.aes_ml) (snd aes.aes_mr)
      ~ep:(aes_ep aes)
      ~dp:{ml; mr; inv = f_real_sub (aes_dp aes).inv delta}
      (aes_pr aes) aes.aes_sl aes.aes_sr {ml; mr; inv = post} in

  let ll1   = f_losslessS aes.aes_ml aes.aes_sl in
  let ll2   = f_losslessS aes.aes_mr aes.aes_sr in
  FApi.xmutate1 tc `APuptobad [ll1; ll2; cond_c; cond_d; cond_a]

(* -------------------------------------------------------------------- *)
let t_utb_l = FApi.t_low1 "utb-l" t_utb_l_r
