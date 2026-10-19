(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The hoare [sp] rule has no parameters: it is stated on the whole
   statement, which must be sp-able. *)
type EcCoreGoal.rule += RHoareSp

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   statement is sp-able, the postcondition is its strongest postcondition)
   are part of it, so the checker re-validates them. *)
let hoare_sp_subgoals (hyps : LDecl.hyps) (hs : sHoareS) : form list =
  let env = LDecl.toenv hyps in
  let rest, sp = EcPlSp.sp_stmt hs.hs_m env hs.hs_s.s_node (hs_pr hs).inv in
  if not (List.is_empty rest) then
    failwith "hoare-sp: the statement is not sp-able";
  if not (EcReduction.is_conv hyps sp (POE.lower (hs_po hs)).inv) then
    failwith "hoare-sp: the postcondition is not the strongest postcondition";
  []

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_hoare_sp (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let subgoals =
    try  hoare_sp_subgoals (FApi.tc1_hyps tc) hs
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc RHoareSp subgoals

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareSp ->
         Some (EcPlRecheck.checker_of "hoare-sp" pf_as_hoareS
                 hoare_sp_subgoals)
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): compute the longest sp-able prefix [c1] of the
   statement up to [at], split there with the [seq] rule using [sp(c1, P)]
   as intermediate assertion, and close the first premise with the rule. *)
let t_hoare_sp_prefix (at : EcMatching.Position.codegap1 option) tc =
  let env = FApi.tc1_env tc in
  let hs  = tc1_as_hoareS tc in
  let c1, _    = o_split ~rev:true env at hs.hs_s in
  let rest, sp = EcPlSp.sp_stmt hs.hs_m env c1 (hs_pr hs).inv in
  EcPlSp.check_sp_progress tc (is_some at) rest;
  let k = List.length c1 - List.length rest in
  let r = EcHoareSeq.{ hsr_at  = EcPlSp.gap_at k;
                       hsr_mid = { m = fst hs.hs_m; inv = sp }; } in
  FApi.t_seqsub (EcHoareSeq.t_hoare_seq r) [t_hoare_sp; EcLowGoal.t_id] tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareS], the position (if any)
   is a single one. *)
let process_hoare_sp (at : EcParsetree.pcodegap1 option) tc =
  let at = Option.map (EcTyping.trans_codegap1 (FApi.tc1_env tc)) at in
  t_hoare_sp_prefix at tc
