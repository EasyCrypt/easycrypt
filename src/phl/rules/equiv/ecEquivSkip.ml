(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The equiv [skip] rule has no parameters. *)
type EcCoreGoal.rule += REquivSkip

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side condition (both
   statements are empty) is part of it, so the checker re-validates it. *)
let equiv_skip_subgoals (es : equivS) : form list =
  if not (List.is_empty es.es_sl.s_node) then
    failwith "equiv-skip: the left statement is not empty";
  if not (List.is_empty es.es_sr.s_node) then
    failwith "equiv-skip: the right statement is not empty";
  let concl = map_ts_inv2 f_imp (es_pr es) (es_po es) in
  [EcSubst.f_forall_mems_ts_inv es.es_ml es.es_mr concl]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_equiv_skip (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  if not (List.is_empty es.es_sl.s_node) then
    tc_error !!tc ~who:"skip" "left instruction list is not empty";
  if not (List.is_empty es.es_sr.s_node) then
    tc_error !!tc ~who:"skip" "right instruction list is not empty";
  FApi.xrule1 tc REquivSkip (equiv_skip_subgoals es)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivSkip ->
         Some (EcPlRecheck.checker_of "equiv-skip" pf_as_equivS
                 (fun _hyps es -> equiv_skip_subgoals es))
     | _ -> None)
