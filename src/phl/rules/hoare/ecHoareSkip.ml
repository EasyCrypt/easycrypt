(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The hoare [skip] rule has no parameters. *)
type EcCoreGoal.rule += RHoareSkip

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side condition (the
   statement is empty) is part of it, so the checker re-validates it. *)
let hoare_skip_subgoals (hs : sHoareS) : form list =
  if not (List.is_empty hs.hs_s.s_node) then
    failwith "hoare-skip: the statement is not empty";
  let post  = POE.lower (hs_po hs) in
  let concl = map_ss_inv2 f_imp (hs_pr hs) post in
  [EcSubst.f_forall_mems_ss_inv hs.hs_m concl]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_hoare_skip (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  if not (List.is_empty hs.hs_s.s_node) then
    tc_error !!tc "instruction list is not empty";
  FApi.xrule1 tc RHoareSkip (hoare_skip_subgoals hs)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareSkip ->
         Some (EcPlRecheck.checker_of "hoare-skip" pf_as_hoareS
                 (fun _hyps hs -> hoare_skip_subgoals hs))
     | _ -> None)
