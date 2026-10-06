(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcAst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The bdhoare [skip] rule has no parameters. *)
type EcCoreGoal.rule += RBdHoareSkip

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   statement is empty, the comparison is [=] or [>=]) are part of it, so the
   checker re-validates them. *)
let bdhoare_skip_subgoals (bhs : bdHoareS) : form list =
  if not (List.is_empty bhs.bhs_s.s_node) then
    failwith "bdhoare-skip: the statement is not empty";
  if bhs.bhs_cmp <> FHeq && bhs.bhs_cmp <> FHge then
    failwith "bdhoare-skip: the comparison is not = or >=";
  let concl = map_ss_inv2 f_imp (bhs_pr bhs) (bhs_po bhs) in
  let concl = EcSubst.f_forall_mems_ss_inv bhs.bhs_m concl in
  if   f_equal (bhs_bd bhs).inv f_r1
  then [concl]
  else [f_eq (bhs_bd bhs).inv f_r1; concl]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_bdhoare_skip (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  if not (List.is_empty bhs.bhs_s.s_node) then
    tc_error !!tc ~who:"skip" "instruction list is not empty";
  if bhs.bhs_cmp <> FHeq && bhs.bhs_cmp <> FHge then
    tc_error !!tc ~who:"skip" "the bound must be compared with = or >=";
  FApi.xrule1 tc RBdHoareSkip (bdhoare_skip_subgoals bhs)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareSkip ->
         Some (EcPlRecheck.checker_of "bdhoare-skip" pf_as_bdhoareS
                 (fun _hyps bhs -> bdhoare_skip_subgoals bhs))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): first turn the goal into [phoare [...] = 1%r]
   with the bound-changing consequence, try to close its side condition,
   then apply the rule.

   TEMPORARY: the bound-changing consequence still comes from the
   not-yet-migrated [EcPhlConseq]. *)
let t_bdhoare_skip_full (tc : tcenv1) =
  let t_trivial = FApi.t_seqs [t_simplify ~delta:`No; t_split; t_fail] in
  let bhs = tc1_as_bdhoareS tc in
  let f_r1 : ss_inv = { m = fst bhs.bhs_m; inv = f_r1 } in
  let t_conseq = EcPhlConseq.t_bdHoareS_conseq_bd FHeq f_r1 in
  FApi.t_internal
    (FApi.t_seqsub t_conseq [FApi.t_try t_trivial; t_bdhoare_skip])
    tc
