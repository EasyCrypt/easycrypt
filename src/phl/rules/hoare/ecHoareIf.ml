(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The hoare [if] rule has no parameters: the statement is the
   conditional. *)
type EcCoreGoal.rule += RHoareIf

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side condition (the
   statement is a single conditional) is part of it, so the checker
   re-validates it. *)
let hoare_if_subgoals (hs : sHoareS) : form list =
  let e, c1, c2 =
    match hs.hs_s.s_node with
    | [{ i_node = Sif (e, c1, c2) }] -> (e, c1, c2)
    | _ -> failwith "hoare-if: the statement is not a single conditional" in
  let b   = ss_inv_of_expr (fst hs.hs_m) e in
  let mt  = snd hs.hs_m in
  let pre = map_ss_inv2 f_and (hs_pr hs) in
  [f_hoareS mt (pre b) c1 (hs_po hs);
   f_hoareS mt (pre (map_ss_inv1 f_not b)) c2 (hs_po hs)]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_hoare_if (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let sg =
    try  hoare_if_subgoals hs
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc RHoareIf sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareIf ->
         Some (EcPlRecheck.checker_of "hoare-if" pf_as_hoareS
                 (fun _hyps hs -> hoare_if_subgoals hs))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): on [if b then c1 else c2; c], push [c] into the
   branches (when not empty), then apply the rule. *)
let t_hoare_if_head (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let _, c = tc1_first_if tc hs.hs_s in
  if List.is_empty c.s_node then t_hoare_if tc else
    FApi.t_seq
      (EcHoareTransform.t_hoare_transform { htr_tr = EcTrIfPush.TrIfPush })
      t_hoare_if tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareS]. *)
let process_hoare_if (info : pcond_info) (tc : tcenv1) =
  match info with
  | `Head _ -> t_hoare_if_head tc
  | `Seq _ | `SeqOne _ -> tc_error_noXhl ~kinds:[`Equiv `Stmt] !!tc
