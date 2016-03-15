(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcCoreGoal
open EcLowPhlGoal

module Mid = EcIdent.Mid
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
module IAPRHL : sig
  val loaded : EcEnv.env -> bool
  val sumr   : form -> form -> form
end = struct
  let i_Aprhl = "Aprhl"
  let p_Aprhl = EcPath.pqname EcCoreLib.p_top i_Aprhl

  let sumr =
    let bgty = [tint; tfun tint treal] in
    let bg   = EcPath.pqname p_Aprhl "sumr" in
    let bg   = f_op bg [] (toarrow bgty treal) in
    fun n f -> f_app bg [n; f] treal

  let loaded (env : EcEnv.env) =
    is_some (EcEnv.Theory.by_path_opt p_Aprhl env)
end


(* -------------------------------------------------------------------- *)
let t_tohoare_r (tc : tcenv1) =
  match f_node (FApi.tc1_goal tc) with
  | FahoareF ahf ->
     let concl = f_hoareF ahf.ahf_pr ahf.ahf_f ahf.ahf_po in
     let bp = f_real_le f_r0 ahf.ahf_b in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToHoare [bp; concl])
       EcLowGoal.t_trivial tc

  | FahoareS ahs ->
     let concl =
       f_hoareS ahs.ahs_m ahs.ahs_pr ahs.ahs_s ahs.ahs_po in
     let bp = f_real_le f_r0 ahs.ahs_b in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToHoare [bp; concl])
       EcLowGoal.t_trivial tc

  | _ -> tc_error_noXhl ~kinds:[`AHoare `Any] !!tc

(* -------------------------------------------------------------------- *)
let t_ofhoare_r (tc : tcenv1) =
  match f_node (FApi.tc1_goal tc) with
  | FhoareF hf ->
     let concl =
       f_ahoareF ~b:f_r0 hf.hf_pr hf.hf_f hf.hf_po in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToHoare [concl])
       EcLowGoal.t_trivial tc

  | FhoareS hs ->
     let concl =
       f_ahoareS ~b:f_r0  hs.hs_m hs.hs_pr hs.hs_s hs.hs_po in
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
     let concl = f_equivF aef.aef_pr aef.aef_fl aef.aef_fr aef.aef_po in
     let ep = f_real_le f_r0 aef.aef_ep in
     let dp = f_real_le f_r0 aef.aef_dp in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToEquiv [ep; dp; concl])
       EcLowGoal.t_trivial tc

  | FaequivS aes ->
     let concl =
       f_equivS aes.aes_ml aes.aes_mr
         aes.aes_pr aes.aes_sl aes.aes_sr aes.aes_po in
     let ep = f_real_le f_r0 aes.aes_ep in
     let dp = f_real_le f_r0 aes.aes_dp in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToEquiv [ep; dp; concl])
       EcLowGoal.t_trivial tc

  | _ -> tc_error_noXhl ~kinds:[`AEquiv `Any] !!tc

(* -------------------------------------------------------------------- *)
let t_ofequiv_r (tc : tcenv1) =
  match f_node (FApi.tc1_goal tc) with
  | FequivF ef ->
     let concl =
       f_aequivF ~ep:f_r0 ~dp:f_r0
         ef.ef_pr ef.ef_fl ef.ef_fr ef.ef_po in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToEquiv [concl])
       EcLowGoal.t_trivial tc

  | FequivS es ->
     let concl =
       f_aequivS ~ep:f_r0 ~dp:f_r0
         es.es_ml es.es_mr es.es_pr es.es_sl es.es_sr es.es_po in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToEquiv [concl])
       EcLowGoal.t_trivial tc

  | _ -> tc_error_noXhl ~kinds:[`AEquiv `Any] !!tc

(* -------------------------------------------------------------------- *)
let t_toequiv = FApi.t_low0 "to-equiv" t_toequiv_r
let t_ofequiv = FApi.t_low0 "ofx-equiv" t_ofequiv_r

(* -------------------------------------------------------------------- *)
let rec t_lap_r (mode : lap_mode) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let aes = tc1_as_aequivS tc in

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

      let f1 = form_of_expr (fst aes.aes_ml) a1 in
      let f2 = form_of_expr (fst aes.aes_mr) a2 in

      let f_lap1 = f_int_le (f_int_abs (f_int_add k (f_int_sub f1 f2))) k'
      and f_lap2 =
        f_eq
          (f_int_add (f_pvar x1 ty1 (fst aes.aes_ml)) k)
          (f_pvar x2 ty2 (fst aes.aes_mr))
      in

      let eqe    = f_eq (form_of_expr mhr e1) (form_of_expr mhr e2) in
      let ep     = f_real_le (f_real_mul (f_real_of_int k') aes.aes_ep) aes.aes_ep in
      let dp     = f_real_le f_r0 aes.aes_dp in
      let k'ge0  = f_int_le f_i0 k' in
      let concl1 = f_imp aes.aes_pr f_lap1 in
      let concl2 = f_imp (f_and aes.aes_pr f_lap2) aes.aes_po in

      (* Check that the \FV(Pre) does not include { x1, x2 } *)
      let concl1 = f_forall_mems [aes.aes_ml; aes.aes_mr] concl1 in
      let concl2 = f_forall_mems [aes.aes_ml; aes.aes_mr] concl2 in

      FApi.t_seq
        (fun tc -> FApi.xmutate1 tc `Lap
          [eqe; ep; dp; k'ge0; concl1; concl2])
        EcLowGoal.t_trivial tc
    end

  | _ -> assert false

(* -------------------------------------------------------------------- *)
let t_lap = FApi.t_low1 "lap" t_lap_r

(* -------------------------------------------------------------------- *)
let t_while_r ((ef, df), (v, inv), n) tc =
  assert (0 <= n);

  if not (IAPRHL.loaded (FApi.tc1_env tc)) then
    tacuerror "awhile: load the `Aprhl' theory first";

  let hyps, _ = FApi.tc1_flat tc in
  let aes = tc1_as_aequivS tc in

  let (b1, s1) = tc1_instr_while tc aes.aes_sl in
  let (b2, s2) = tc1_instr_while tc aes.aes_sr in

  let fb1 = form_of_expr (fst aes.aes_ml) b1 in
  let fb2 = form_of_expr (fst aes.aes_mr) b2 in

  let tb = tfun tint treal in
  let ef = EcProofTyping.process_exp hyps `InOp (Some tb) ef in
  let df = EcProofTyping.process_exp hyps `InOp (Some tb) df in

  let eff = form_of_expr mhr ef in
  let dff = form_of_expr mhr df in

  let v =
    let hyps = EcEnv.LDecl.push_active aes.aes_ml hyps in
    EcProofTyping.pf_process_form !!tc hyps tint v
  in

  let inv =
    let hyps = EcEnv.LDecl.push_all [aes.aes_ml; aes.aes_mr] hyps in
    EcProofTyping.pf_process_formula !!tc hyps inv
  in

  let k  = EcIdent.create "k" in
  let ki = f_local k tint in

  let fn =  f_int (EcBigInt.of_int n) in

  let ef_gt0 =
    f_forall [k, GTty tint] (f_real_le f_r0 (f_app eff [ki] treal)) in

  let df_gt0 =
    f_forall [k, GTty tint] (f_real_le f_r0 (f_app dff [ki] treal)) in

  let term =
    f_forall_mems [aes.aes_ml]
       (f_imp (f_and inv (f_int_lt v f_i0)) (f_not fb1)) in

  let sub =
    let sub_pre = f_ands [inv; fb1; fb2; f_eq ki v; f_int_le v fn] in

    let sub_post = f_ands [inv; f_eq fb1 fb2; f_int_lt v ki] in

    f_forall [k, GTty tint] (
      f_aequivS aes.aes_ml aes.aes_mr
        ~dp:(form_of_expr mhr (e_app df [e_local k tint] treal))
        ~ep:(form_of_expr mhr (e_app ef [e_local k tint] treal))
        sub_pre s1 s2 sub_post)
  in

  let concl1 = f_forall_mems [aes.aes_ml; aes.aes_mr]
    (f_imp aes.aes_pr (
       f_ands [inv; f_eq fb1 fb2; f_int_lt v fn])) in

  let concl2 = f_forall_mems [aes.aes_ml; aes.aes_mr]
    (f_imp (f_ands [inv; f_not fb1; f_not fb2]) aes.aes_po) in

  let sume, sumd =
    (f_eq aes.aes_ep (IAPRHL.sumr fn eff),
     f_eq aes.aes_ep (IAPRHL.sumr fn dff))
  in

  FApi.t_seq
    (fun tc -> FApi.xmutate1 tc `AWhile
       [ef_gt0; df_gt0; term; concl1; concl2; sume; sumd; sub])
    (FApi.t_seq EcLowGoal.t_simplify EcLowGoal.t_trivial) tc

(* -------------------------------------------------------------------- *)
let t_while = FApi.t_low1 "awhile" t_while_r
