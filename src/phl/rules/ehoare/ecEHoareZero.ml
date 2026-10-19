(* -------------------------------------------------------------------- *)
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The ehoare [zero] rules have no parameters. *)
type EcCoreGoal.rule +=
  | REHoareSZero
  | REHoareFZero

(* -------------------------------------------------------------------- *)
let f_xr0 = f_r2xr f_r0

(* Pure cores shared by the rules and their checkers: no premise; the side
   condition (the postcondition is syntactically [0%xr]) is part of them, so
   the checker re-validates it. *)
let ehoareS_zero_subgoals (hs : eHoareS) : form list =
  if not (f_equal (ehs_po hs).inv f_xr0) then
    failwith "ehoareS-zero: the postcondition is not 0%xr";
  []

let ehoareF_zero_subgoals (hf : eHoareF) : form list =
  if not (f_equal (ehf_po hf).inv f_xr0) then
    failwith "ehoareF-zero: the postcondition is not 0%xr";
  []

(* -------------------------------------------------------------------- *)
let not_of_the_form tc =
  tc_error !!tc "the conclusion is not of the form %s" "ehoare[_ : _ ==> 0%xr]"

(* Rules (TCB). *)
let t_ehoareS_zero (tc : tcenv1) =
  let hs = tc1_as_ehoareS tc in
  if not (f_equal (ehs_po hs).inv f_xr0) then not_of_the_form tc;
  FApi.xrule1 tc REHoareSZero (ehoareS_zero_subgoals hs)

let t_ehoareF_zero (tc : tcenv1) =
  let hf = tc1_as_ehoareF tc in
  if not (f_equal (ehf_po hf).inv f_xr0) then not_of_the_form tc;
  FApi.xrule1 tc REHoareFZero (ehoareF_zero_subgoals hf)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareSZero ->
         Some (EcPlRecheck.checker_of "ehoareS-zero" pf_as_ehoareS
                 (fun _hyps hs -> ehoareS_zero_subgoals hs))
     | REHoareFZero ->
         Some (EcPlRecheck.checker_of "ehoareF-zero" pf_as_ehoareF
                 (fun _hyps hf -> ehoareF_zero_subgoals hf))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Dispatcher (no node of its own). *)
let t_ehoare_zero (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FeHoareS _ -> t_ehoareS_zero tc
  | FeHoareF _ -> t_ehoareF_zero tc
  | _          -> not_of_the_form tc
