(* -------------------------------------------------------------------- *)
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)

let t_hoare_true_r tc =
  match (FApi.tc1_goal tc).f_node with
  | FhoareF hf when forall_poe (f_equal f_true) (hf_po hf).hsi_inv ->
      FApi.xmutate1 tc `HoareTrue []

  | FhoareS hs when forall_poe (f_equal f_true) (hs_po hs).hsi_inv ->
      FApi.xmutate1 tc `HoareTrue []

  | _ ->
    tc_error !!tc
      "the conclusion is not of the form %s"
      "hoare[_ : _ ==> true]"

let t_hoare_true = FApi.t_low0 "hoare-true" t_hoare_true_r

(* -------------------------------------------------------------------- *)
let f_xr0 = f_r2xr f_r0

let t_ehoare_zero_r tc =
  match (FApi.tc1_goal tc).f_node with
  | FeHoareF hf when f_equal (ehf_po hf).inv f_xr0 ->
       FApi.xmutate1 tc `eHoareZero []

  | FeHoareS hs when f_equal (ehs_po hs).inv f_xr0 ->
       FApi.xmutate1 tc `eHoareZero []
  | _ ->
    tc_error !!tc
      "the conclusion is not of the form %s"
      "ehoare[_ : _ ==> 0%xr]"

let t_ehoare_zero = FApi.t_low0 "hoare-zero" t_ehoare_zero_r

(* -------------------------------------------------------------------- *)
let t_core_exfalso_r tc =
  let pre   = tc1_get_pre tc in
    if not (f_equal (inv_of_inv pre) f_false) then
      tc_error !!tc "pre-condition is not `false'";
    FApi.xmutate1 tc `ExFalso []

let t_core_exfalso = FApi.t_low0 "core-exfalso" t_core_exfalso_r
