(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The ehoare [skip] rule has no parameters. *)
type EcCoreGoal.rule += REHoareSkip

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side condition (the
   statement is empty) is part of it, so the checker re-validates it. *)
let ehoare_skip_subgoals (hs : eHoareS) : form list =
  if not (List.is_empty hs.ehs_s.s_node) then
    failwith "ehoare-skip: the statement is not empty";
  let concl = map_ss_inv2 f_xreal_le (ehs_po hs) (ehs_pr hs) in
  [EcSubst.f_forall_mems_ss_inv hs.ehs_m concl]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_ehoare_skip (tc : tcenv1) =
  let hs = tc1_as_ehoareS tc in
  if not (List.is_empty hs.ehs_s.s_node) then
    tc_error !!tc "instruction list is not empty";
  FApi.xrule1 tc REHoareSkip (ehoare_skip_subgoals hs)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareSkip ->
         Some (EcPlRecheck.checker_of "ehoare-skip" pf_as_ehoareS
                 (fun _hyps hs -> ehoare_skip_subgoals hs))
     | _ -> None)
