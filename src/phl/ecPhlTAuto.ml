(* -------------------------------------------------------------------- *)
open EcFol

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
let t_hoare_true_r tc =
  match (FApi.tc1_goal tc).f_node with
  | FhoareF hf when f_equal hf.hf_po f_true ->
      FApi.xmutate1 tc `HoareTrue []

  | FhoareS hs when f_equal hs.hs_po f_true ->
      FApi.xmutate1 tc `HoareTrue []

  | _ ->
    tc_error !!tc
      "the conclusion is not of the form %s"
      "hoare[_ : _ ==> true]"

let t_hoare_true = FApi.t_low0 "hoare-true" t_hoare_true_r

(* -------------------------------------------------------------------- *)
let t_core_exfalso_r tc =
  let pre   = tc1_get_pre tc in
    if not (f_equal pre f_false) then
      tc_error !!tc "pre-condition is not `false'";
    FApi.xmutate1 tc `ExFalso []

let t_core_exfalso = FApi.t_low0 "core-exfalso" t_core_exfalso_r
