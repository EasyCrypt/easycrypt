(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The bdhoare [if] rule has no parameters: the statement is the
   conditional. *)
type EcCoreGoal.rule += RBdHoareIf

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side condition (the
   statement is a single conditional) is part of it, so the checker
   re-validates it. *)
let bdhoare_if_subgoals (bhs : bdHoareS) : form list =
  let e, c1, c2 =
    match bhs.bhs_s.s_node with
    | [{ i_node = Sif (e, c1, c2) }] -> (e, c1, c2)
    | _ -> failwith "bdhoare-if: the statement is not a single conditional" in
  let b  = ss_inv_of_expr (fst bhs.bhs_m) e in
  let mt = snd bhs.bhs_m in
  let concl b s =
    f_bdHoareS mt (map_ss_inv2 f_and (bhs_pr bhs) b) s
      (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs) in
  [concl b c1; concl (map_ss_inv1 f_not b) c2]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_bdhoare_if (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  let sg =
    try  bdhoare_if_subgoals bhs
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc RBdHoareIf sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareIf ->
         Some (EcPlRecheck.checker_of "bdhoare-if" pf_as_bdhoareS
                 (fun _hyps bhs -> bdhoare_if_subgoals bhs))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): on [if b then c1 else c2; c], push [c] into the
   branches (when not empty), then apply the rule. *)
let t_bdhoare_if_head (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  let _, c = tc1_first_if tc bhs.bhs_s in
  if List.is_empty c.s_node then t_bdhoare_if tc else
    FApi.t_seq
      (EcBdHoareTransform.t_bdhoare_transform { btr_tr = EcTrIfPush.TrIfPush })
      t_bdhoare_if tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [bdHoareS]. *)
let process_bdhoare_if (info : pcond_info) (tc : tcenv1) =
  match info with
  | `Head _ -> t_bdhoare_if_head tc
  | `Seq _ | `SeqOne _ -> tc_error_noXhl ~kinds:[`Equiv `Stmt] !!tc
