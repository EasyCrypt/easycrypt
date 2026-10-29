(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The ehoare [if] rule has no parameters: the statement is the
   conditional. *)
type EcCoreGoal.rule += REHoareIf

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side condition (the
   statement is a single conditional) is part of it, so the checker
   re-validates it. *)
let ehoare_if_subgoals (hs : eHoareS) : form list =
  let e, c1, c2 =
    match hs.ehs_s.s_node with
    | [{ i_node = Sif (e, c1, c2) }] -> (e, c1, c2)
    | _ -> failwith "ehoare-if: the statement is not a single conditional" in
  let b   = ss_inv_of_expr (fst hs.ehs_m) e in
  let mt  = snd hs.ehs_m in
  let pre b = map_ss_inv2 f_interp_ehoare_form b (ehs_pr hs) in
  [f_eHoareS mt (pre b) c1 (ehs_po hs);
   f_eHoareS mt (pre (map_ss_inv1 f_not b)) c2 (ehs_po hs)]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_ehoare_if (tc : tcenv1) =
  let hs = tc1_as_ehoareS tc in
  let sg =
    try  ehoare_if_subgoals hs
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc REHoareIf sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareIf ->
         Some (EcPlRecheck.checker_of "ehoare-if" pf_as_ehoareS
                 (fun _hyps hs -> ehoare_if_subgoals hs))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): on [if b then c1 else c2; c], push [c] into the
   branches (when not empty), then apply the rule. *)
let t_ehoare_if_head (tc : tcenv1) =
  let hs = tc1_as_ehoareS tc in
  let _, c = tc1_first_if tc hs.ehs_s in
  if List.is_empty c.s_node then t_ehoare_if tc else
    FApi.t_seq
      (EcEHoareTransform.t_ehoare_transform { ehtr_tr = EcTrIfPush.TrIfPush })
      t_ehoare_if tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [eHoareS]. *)
let process_ehoare_if (info : pcond_info) (tc : tcenv1) =
  match info with
  | `Head _ -> t_ehoare_if_head tc
  | `Seq _ | `SeqOne _ -> tc_error_noXhl ~kinds:[`Equiv `Stmt] !!tc
