(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal
open EcPlWeakMem

(* -------------------------------------------------------------------- *)
(* Parameter of the ehoare [weakmem] rule: the variables declared in the
   goal's memory, typed. Nothing to resolve: the same record is the rule
   argument and the node payload. *)
type ehoare_weakmem = {
  ehwm_vars : ovariable list;
}

type EcCoreGoal.rule += REHoareWeakMem of ehoare_weakmem

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   variables are the last ones declared in the memory, fresh in the rest
   of it, and not used by the judgement) are re-checked by
   [EcPlWeakMem.restrict], so the checker re-validates them. *)
let ehoare_weakmem_subgoals
    (hyps : LDecl.hyps) (hs : eHoareS) (n : ehoare_weakmem)
=
  let env  = LDecl.toenv hyps in
  let used =
    used env (fst hs.ehs_m) hs.ehs_s [hs.ehs_pr; hs.ehs_po] in
  [f_eHoareS_r { hs with ehs_m = restrict env n.ehwm_vars hs.ehs_m used }]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_ehoare_weakmem (r : ehoare_weakmem) (tc : tcenv1) =
  let hs = tc1_as_ehoareS tc in
  let sg =
    try  ehoare_weakmem_subgoals (FApi.tc1_hyps tc) hs r
    with InvalidWeakening msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (REHoareWeakMem r) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareWeakMem n ->
         Some (EcPlRecheck.checker_of "ehoare-weakmem" pf_as_ehoareS
                 (fun hyps hs -> ehoare_weakmem_subgoals hyps hs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): cut the hypothesis [h] weakened by the
   variables, close the cut judgement by the rule and [h]. Raises
   [EcMemory.DuplicatedMemoryBinding] (before acting) when a variable is
   already declared. *)
let t_ehoare_weakmem_hyp (h : EcIdent.t) (r : ehoare_weakmem) (tc : tcenv1) =
  let hs = destr_eHoareS (LDecl.hyp_by_id h (FApi.tc1_hyps tc)) in
  let hs = { hs with ehs_m = EcMemory.bindall r.ehwm_vars hs.ehs_m } in
  FApi.t_first
    (FApi.t_seq (t_ehoare_weakmem r) (EcLowGoal.t_apply_hyp h ~args:[] ~sk:0))
    (EcLowGoal.t_cut (f_eHoareS_r hs) tc)
