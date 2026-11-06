(* -------------------------------------------------------------------- *)
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The hoare [exfalso] rules have no parameters. *)
type EcCoreGoal.rule +=
  | RHoareSExfalso
  | RHoareFExfalso

(* -------------------------------------------------------------------- *)
(* Pure cores shared by the rules and their checkers: no premise; the side
   condition (the precondition is syntactically [false]) is part of them, so
   the checker re-validates it. *)
let hoareS_exfalso_subgoals (hs : sHoareS) : form list =
  if not (f_equal (hs_pr hs).inv f_false) then
    failwith "hoareS-exfalso: the precondition is not false";
  []

let hoareF_exfalso_subgoals (hf : sHoareF) : form list =
  if not (f_equal (hf_pr hf).inv f_false) then
    failwith "hoareF-exfalso: the precondition is not false";
  []

(* -------------------------------------------------------------------- *)
let not_false tc = tc_error !!tc "pre-condition is not `false'"

(* Rules (TCB). *)
let t_hoareS_exfalso (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  if not (f_equal (hs_pr hs).inv f_false) then not_false tc;
  FApi.xrule1 tc RHoareSExfalso (hoareS_exfalso_subgoals hs)

let t_hoareF_exfalso (tc : tcenv1) =
  let hf = tc1_as_hoareF tc in
  if not (f_equal (hf_pr hf).inv f_false) then not_false tc;
  FApi.xrule1 tc RHoareFExfalso (hoareF_exfalso_subgoals hf)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareSExfalso ->
         Some (EcPlRecheck.checker_of "hoareS-exfalso" pf_as_hoareS
                 (fun _hyps hs -> hoareS_exfalso_subgoals hs))
     | RHoareFExfalso ->
         Some (EcPlRecheck.checker_of "hoareF-exfalso" pf_as_hoareF
                 (fun _hyps hf -> hoareF_exfalso_subgoals hf))
     | _ -> None)
