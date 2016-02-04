(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypes
open EcFol
open EcCoreGoal
open EcLowPhlGoal

module Mid = EcIdent.Mid
module TTC = EcProofTyping

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
  | `Null k -> begin
      let k   = TTC.tc1_process_form tc tint k in
      let rd1 = EcPV.e_read_r env EcPV.PV.empty a1 in
      let rd2 = EcPV.e_read_r env EcPV.PV.empty a2 in
(* FIXME:     let rf  = EcPV.f_read_r env EcPV.PV.empty aes.aes_pr in*)

      if EcPV.PV.mem_pv env x1 rd1 || EcPV.PV.mem_pv env x2 rd2 then
        tc_error !!tc "lvalue of rnd-lap cannot occur in the lap argument";

      let f1 = form_of_expr (fst aes.aes_ml) a1 in
      let f2 = form_of_expr (fst aes.aes_mr) a2 in

      let f_lap1 = f_int_le (f_int_abs (f_int_sub f1 f2)) k
      and f_lap2 =
        f_int_le
          (f_int_abs
             (f_int_sub 
                (f_pvar x1 ty1 (fst aes.aes_ml))
                (f_pvar x2 ty2 (fst aes.aes_mr))))
          k
      in

      let eqe    = f_eq (form_of_expr mhr e1) (form_of_expr mhr e2) in
      let ep     = f_real_le f_r0 aes.aes_ep in
      let dp     = f_real_le f_r0 aes.aes_dp in
      let concl1 = f_imp aes.aes_pr f_lap1 in
      let concl2 = f_imp (f_and aes.aes_pr f_lap2) aes.aes_po in

      let concl1 = f_forall_mems [aes.aes_ml; aes.aes_mr] concl1 in
      let concl2 = f_forall_mems [aes.aes_ml; aes.aes_mr] concl2 in

      FApi.t_seq
        (fun tc -> FApi.xmutate1 tc `Lap [eqe; ep; dp; concl1; concl2])
        EcLowGoal.t_trivial tc
    end

  | `Gen _ -> begin assert false
(*
     let k  = TTC.tc1_process_form tc treal k  in
     let k' = TTC.tc1_process_form tc treal k' in

     let e1 = form_of_expr mhr e1 in
     let e2 = form_of_expr mhr e2 in
     let a1 = form_of_expr (fst aes.aes_ml) a1 in
     let a2 = form_of_expr (fst aes.aes_mr) a2 in

     let eqe = f_eq e1 e2 in
     let eqk = f_eq (f_real_mul k' e1) aes.aes_ep in
     let ep  = f_real_le f_r0 aes.aes_ep in
     let dp  = f_real_le f_r0 aes.aes_dp in

     let f_pr =
       f_real_le
         (f_real_abs (f_real_sub (f_real_add k a1) a2))
         k'

     and f_po =
       f_eq
         (f_real_add (f_pvar x1 ty1 (fst aes.aes_ml)) k)
         (f_pvar x2 ty2 (fst aes.aes_ml))
     in

     let concl1 = f_imp aes.aes_pr f_pr in
     let concl2 = f_imp f_po aes.aes_po in

      FApi.t_seq
        (fun tc -> FApi.xmutate1 tc `Lap
           [eqe; eqk; ep; dp; concl1; concl2])
        EcLowGoal.t_trivial tc
 *)
    end

(*-------------------------------------------------------------------- *)
let t_lap = FApi.t_low1 "lap" t_lap_r
