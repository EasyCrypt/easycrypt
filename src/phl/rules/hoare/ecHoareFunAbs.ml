(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypes
open EcFol
open EcAst
open EcModules
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameter of the hoare abstract-procedure rule: the invariant, already
   typed. Nothing to resolve: the same record is the rule argument and the
   node payload. *)
type hoare_fun_abs = {
  hfa_inv : ss_inv;   (* invariant I *)
}

type EcCoreGoal.rule += RHoareFunAbs of hoare_fun_abs

(* -------------------------------------------------------------------- *)
let hoareF_abs_spec (env : env) (f : EcPath.xpath) (inv : ss_inv) =
  let (top, _, oi, _) = EcLowPhlGoal.abstract_info env f in
  let fv = PV.fv env inv.m inv.inv in
  PV.check_depend env fv top;
  let ospec o = f_hoareF inv o (POE.lift inv) in
  let sg = List.map ospec (OI.allowed oi) in
  (inv, inv, sg)

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   procedure is abstract, the invariant does not depend on its globals, the
   goal is [hoare [f : I ==> I]]) are part of it, so the checker
   re-validates them. *)
let hoareF_abs_subgoals (hyps : LDecl.hyps) (hf : sHoareF) (n : hoare_fun_abs) =
  let pre, post, sg = hoareF_abs_spec (LDecl.toenv hyps) hf.hf_f n.hfa_inv in
  if not (   EcReduction.ss_inv_alpha_eq hyps (hf_pr hf) pre
          && EcReduction.hs_inv_alpha_eq hyps (hf_po hf) (POE.lift post)) then
    failwith "hoareF-fun-abs: the judgement is not [I ==> I]";
  sg

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_hoareF_abs (r : hoare_fun_abs) (tc : tcenv1) =
  let hf = tc1_as_hoareF tc in
  FApi.xrule1 tc (RHoareFunAbs r) (hoareF_abs_subgoals (FApi.tc1_hyps tc) hf r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareFunAbs n ->
         Some (EcPlRecheck.checker_of "hoareF-fun-abs" pf_as_hoareF
                 (fun hyps hf -> hoareF_abs_subgoals hyps hf n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): the consequence to [I ==> I], then the rule.

   TEMPORARY: the consequence rule still comes from the not-yet-migrated
   [EcPhlConseq]. *)
let t_hoareF_abs_full (r : hoare_fun_abs) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hf  = tc1_as_hoareF tc in
  let pre, post, _ = hoareF_abs_spec env hf.hf_f r.hfa_inv in
  FApi.t_last (t_hoareF_abs r)
    (EcPhlConseq.t_hoareF_conseq pre (POE.lift post) tc)

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareF]. *)
let process_hoareF_abs (inv : pformula) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let m    = EcIdent.create "&hr" in
  let env' = LDecl.inv_memenv1 m hyps in
  let inv  = TTC.pf_process_form !!tc env' tbool inv in
  t_hoareF_abs_full { hfa_inv = { inv; m; } } tc
