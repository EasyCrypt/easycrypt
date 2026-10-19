(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal
open EcPlWeakMem

(* -------------------------------------------------------------------- *)
(* Parameter of the hoare [weakmem] rule: the variables declared in the
   goal's memory, typed. Nothing to resolve: the same record is the rule
   argument and the node payload. *)
type hoare_weakmem = {
  hwm_vars : ovariable list;
}

type EcCoreGoal.rule += RHoareWeakMem of hoare_weakmem

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   variables are the last ones declared in the memory, fresh in the rest
   of it, and not used by the judgement) are re-checked by
   [EcPlWeakMem.restrict], so the checker re-validates them. *)
let hoare_weakmem_subgoals
    (hyps : LDecl.hyps) (hs : sHoareS) (n : hoare_weakmem)
=
  let env  = LDecl.toenv hyps in
  let used =
    used env (fst hs.hs_m) hs.hs_s (hs.hs_pr :: POE.to_list hs.hs_po) in
  [f_hoareS_r { hs with hs_m = restrict env n.hwm_vars hs.hs_m used }]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_hoare_weakmem (r : hoare_weakmem) (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let sg =
    try  hoare_weakmem_subgoals (FApi.tc1_hyps tc) hs r
    with InvalidWeakening msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (RHoareWeakMem r) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareWeakMem n ->
         Some (EcPlRecheck.checker_of "hoare-weakmem" pf_as_hoareS
                 (fun hyps hs -> hoare_weakmem_subgoals hyps hs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): cut the hypothesis [h] weakened by the
   variables, close the cut judgement by the rule and [h]. Raises
   [EcMemory.DuplicatedMemoryBinding] (before acting) when a variable is
   already declared. *)
let t_hoare_weakmem_hyp (h : EcIdent.t) (r : hoare_weakmem) (tc : tcenv1) =
  let hs = destr_hoareS (LDecl.hyp_by_id h (FApi.tc1_hyps tc)) in
  let hs = { hs with hs_m = EcMemory.bindall r.hwm_vars hs.hs_m } in
  FApi.t_first
    (FApi.t_seq (t_hoare_weakmem r) (EcLowGoal.t_apply_hyp h ~args:[] ~sk:0))
    (EcLowGoal.t_cut (f_hoareS_r hs) tc)
