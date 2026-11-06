(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcAst
open EcModules
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameter of the ehoare abstract-procedure rule: the invariant, already
   typed. Nothing to resolve: the same record is the rule argument and the
   node payload. *)
type ehoare_fun_abs = {
  ehfa_inv : ss_inv;   (* invariant I *)
}

type EcCoreGoal.rule += REHoareFunAbs of ehoare_fun_abs

(* -------------------------------------------------------------------- *)
let ehoareF_abs_spec (env : env) (f : EcPath.xpath) (inv : ss_inv) =
  let (top, _, oi, _) = EcLowPhlGoal.abstract_info env f in
  let fv = PV.fv env inv.m inv.inv in
  PV.check_depend env fv top;
  let ospec o = f_eHoareF inv o inv in
  let sg = List.map ospec (OI.allowed oi) in
  (inv, inv, sg)

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   procedure is abstract, the invariant does not depend on its globals, the
   goal is [ehoare [f : I ==> I]]) are part of it, so the checker
   re-validates them. *)
let ehoareF_abs_subgoals (hyps : LDecl.hyps) (hf : eHoareF) (n : ehoare_fun_abs) =
  let pre, post, sg = ehoareF_abs_spec (LDecl.toenv hyps) hf.ehf_f n.ehfa_inv in
  if not (   EcReduction.ss_inv_alpha_eq hyps (ehf_pr hf) pre
          && EcReduction.ss_inv_alpha_eq hyps (ehf_po hf) post) then
    failwith "ehoareF-fun-abs: the judgement is not [I ==> I]";
  sg

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_ehoareF_abs (r : ehoare_fun_abs) (tc : tcenv1) =
  let hf = tc1_as_ehoareF tc in
  FApi.xrule1 tc (REHoareFunAbs r) (ehoareF_abs_subgoals (FApi.tc1_hyps tc) hf r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareFunAbs n ->
         Some (EcPlRecheck.checker_of "ehoareF-fun-abs" pf_as_ehoareF
                 (fun hyps hf -> ehoareF_abs_subgoals hyps hf n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): the consequence to [I ==> I], then the rule.

   TEMPORARY: the consequence rule still comes from the not-yet-migrated
   [EcPhlConseq]. *)
let t_ehoareF_abs_full (r : ehoare_fun_abs) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hf  = tc1_as_ehoareF tc in
  let pre, post, _ = ehoareF_abs_spec env hf.ehf_f r.ehfa_inv in
  FApi.t_last (t_ehoareF_abs r) (EcPhlConseq.t_ehoareF_conseq pre post tc)

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [ehoareF]. *)
let process_ehoareF_abs (inv : pformula) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let m    = EcIdent.create "&hr" in
  let env' = LDecl.inv_memenv1 m hyps in
  let inv  = TTC.pf_process_xreal !!tc env' inv in
  t_ehoareF_abs_full { ehfa_inv = { inv; m; } } tc
