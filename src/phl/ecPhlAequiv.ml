(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcFol
open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
let t_toequiv_r (tc : tcenv1) =
  match f_node (FApi.tc1_goal tc) with
  | FaequivF aef ->
     let concl = f_equivF aef.aef_pr aef.aef_fl aef.aef_fr aef.aef_po in
     let dp = f_real_le f_r0 aef.aef_dp in
     let ep = f_real_le f_r0 aef.aef_ep in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToEquiv [dp; ep; concl])
       EcLowGoal.t_trivial tc

  | FaequivS aes ->
     let concl =
       f_equivS aes.aes_ml aes.aes_mr
         aes.aes_pr aes.aes_sl aes.aes_sr aes.aes_po in
     let dp = f_real_le f_r0 aes.aes_dp in
     let ep = f_real_le f_r0 aes.aes_ep in
     FApi.t_seq
       (fun tc -> FApi.xmutate1 tc `ToEquiv [dp; ep; concl])
       EcLowGoal.t_trivial tc

  | _ -> tc_error_noXhl ~kinds:[`AEquiv `Any] !!tc

(* -------------------------------------------------------------------- *)
let t_toequiv = FApi.t_low0 "to-equiv" t_toequiv_r
