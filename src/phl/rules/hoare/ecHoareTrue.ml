(* -------------------------------------------------------------------- *)
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The hoare [true] rules have no parameters. *)
type EcCoreGoal.rule +=
  | RHoareSTrue
  | RHoareFTrue

(* -------------------------------------------------------------------- *)
(* Every postcondition, normal and exceptional, is syntactically [true]. *)
let is_true_post (po : hs_inv) =
  POE.forall (f_equal f_true) po.hsi_inv

(* Pure cores shared by the rules and their checkers: no premise; the side
   condition is part of them, so the checker re-validates it. *)
let hoareS_true_subgoals (hs : sHoareS) : form list =
  if not (is_true_post (hs_po hs)) then
    failwith "hoareS-true: the postcondition is not true";
  []

let hoareF_true_subgoals (hf : sHoareF) : form list =
  if not (is_true_post (hf_po hf)) then
    failwith "hoareF-true: the postcondition is not true";
  []

(* -------------------------------------------------------------------- *)
let not_of_the_form tc =
  tc_error !!tc "the conclusion is not of the form %s" "hoare[_ : _ ==> true]"

(* Rules (TCB). *)
let t_hoareS_true (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  if not (is_true_post (hs_po hs)) then not_of_the_form tc;
  FApi.xrule1 tc RHoareSTrue (hoareS_true_subgoals hs)

let t_hoareF_true (tc : tcenv1) =
  let hf = tc1_as_hoareF tc in
  if not (is_true_post (hf_po hf)) then not_of_the_form tc;
  FApi.xrule1 tc RHoareFTrue (hoareF_true_subgoals hf)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareSTrue ->
         Some (EcPlRecheck.checker_of "hoareS-true" pf_as_hoareS
                 (fun _hyps hs -> hoareS_true_subgoals hs))
     | RHoareFTrue ->
         Some (EcPlRecheck.checker_of "hoareF-true" pf_as_hoareF
                 (fun _hyps hf -> hoareF_true_subgoals hf))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Dispatcher (no node of its own). *)
let t_hoare_true (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FhoareS _ -> t_hoareS_true tc
  | FhoareF _ -> t_hoareF_true tc
  | _         -> not_of_the_form tc
