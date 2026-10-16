(* -------------------------------------------------------------------- *)
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The equiv [exfalso] rules have no parameters. *)
type EcCoreGoal.rule +=
  | REquivSExfalso
  | REquivFExfalso

(* -------------------------------------------------------------------- *)
(* Pure cores shared by the rules and their checkers: no premise; the side
   condition (the precondition is syntactically [false]) is part of them, so
   the checker re-validates it. *)
let equivS_exfalso_subgoals (es : equivS) : form list =
  if not (f_equal (es_pr es).inv f_false) then
    failwith "equivS-exfalso: the precondition is not false";
  []

let equivF_exfalso_subgoals (ef : equivF) : form list =
  if not (f_equal (ef_pr ef).inv f_false) then
    failwith "equivF-exfalso: the precondition is not false";
  []

(* -------------------------------------------------------------------- *)
let not_false tc = tc_error !!tc "pre-condition is not `false'"

(* Rules (TCB). *)
let t_equivS_exfalso (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  if not (f_equal (es_pr es).inv f_false) then not_false tc;
  FApi.xrule1 tc REquivSExfalso (equivS_exfalso_subgoals es)

let t_equivF_exfalso (tc : tcenv1) =
  let ef = tc1_as_equivF tc in
  if not (f_equal (ef_pr ef).inv f_false) then not_false tc;
  FApi.xrule1 tc REquivFExfalso (equivF_exfalso_subgoals ef)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivSExfalso ->
         Some (EcPlRecheck.checker_of "equivS-exfalso" pf_as_equivS
                 (fun _hyps es -> equivS_exfalso_subgoals es))
     | REquivFExfalso ->
         Some (EcPlRecheck.checker_of "equivF-exfalso" pf_as_equivF
                 (fun _hyps ef -> equivF_exfalso_subgoals ef))
     | _ -> None)
