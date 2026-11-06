(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal
open EcPlWeakMem

(* -------------------------------------------------------------------- *)
(* Parameter of the bdhoare [weakmem] rule: the variables declared in the
   goal's memory, typed. Nothing to resolve: the same record is the rule
   argument and the node payload. *)
type bdhoare_weakmem = {
  bwm_vars : ovariable list;
}

type EcCoreGoal.rule += RBdHoareWeakMem of bdhoare_weakmem

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   variables are the last ones declared in the memory, fresh in the rest
   of it, and not used by the judgement) are re-checked by
   [EcPlWeakMem.restrict], so the checker re-validates them. *)
let bdhoare_weakmem_subgoals
    (hyps : LDecl.hyps) (hs : bdHoareS) (n : bdhoare_weakmem)
=
  let env  = LDecl.toenv hyps in
  let used =
    used env (fst hs.bhs_m) hs.bhs_s [hs.bhs_pr; hs.bhs_po; hs.bhs_bd] in
  [f_bdHoareS_r { hs with bhs_m = restrict env n.bwm_vars hs.bhs_m used }]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_bdhoare_weakmem (r : bdhoare_weakmem) (tc : tcenv1) =
  let hs = tc1_as_bdhoareS tc in
  let sg =
    try  bdhoare_weakmem_subgoals (FApi.tc1_hyps tc) hs r
    with InvalidWeakening msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (RBdHoareWeakMem r) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareWeakMem n ->
         Some (EcPlRecheck.checker_of "bdhoare-weakmem" pf_as_bdhoareS
                 (fun hyps hs -> bdhoare_weakmem_subgoals hyps hs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): cut the hypothesis [h] weakened by the
   variables, close the cut judgement by the rule and [h]. Raises
   [EcMemory.DuplicatedMemoryBinding] (before acting) when a variable is
   already declared. *)
let t_bdhoare_weakmem_hyp (h : EcIdent.t) (r : bdhoare_weakmem) (tc : tcenv1) =
  let hs = destr_bdHoareS (LDecl.hyp_by_id h (FApi.tc1_hyps tc)) in
  let hs = { hs with bhs_m = EcMemory.bindall r.bwm_vars hs.bhs_m } in
  FApi.t_first
    (FApi.t_seq (t_bdhoare_weakmem r) (EcLowGoal.t_apply_hyp h ~args:[] ~sk:0))
    (EcLowGoal.t_cut (f_bdHoareS_r hs) tc)
