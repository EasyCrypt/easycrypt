(* -------------------------------------------------------------------- *)
open EcAst

open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* The rules behind the [hoare] tactic (views between hoare and
   probability-0 bdhoare judgements) and the bdhoare [split] rules live in
   [rules/<logic>/]. This module only keeps the dispatcher and the legacy
   positional entry points. *)
let t_hoare_bd_hoare (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FbdHoareF _ -> EcBdHoareOfHoare.t_bdhoareF_of_hoare_full tc
  | FbdHoareS _ -> EcBdHoareOfHoare.t_bdhoareS_of_hoare_full tc
  | FhoareF   _ -> EcHoareOfBdHoare.t_hoareF_of_bdhoare tc
  | FhoareS   _ -> EcHoareOfBdHoare.t_hoareS_of_bdhoare tc
  | _ -> tc_error !!tc "a hoare or phoare judgment was expected"

(* -------------------------------------------------------------------- *)
let t_bdhoare_and b1 b2 b3 =
  EcBdHoareSplit.(t_bdhoare_split_and { bsb_b1 = b1; bsb_b2 = b2; bsb_b3 = b3; })

let t_bdhoare_or b1 b2 b3 =
  EcBdHoareSplit.(t_bdhoare_split_or { bsb_b1 = b1; bsb_b2 = b2; bsb_b3 = b3; })

let t_bdhoare_not b1 b2 =
  EcBdHoareSplit.(t_bdhoare_split_not { bnt_b1 = b1; bnt_b2 = b2; })
