(* -------------------------------------------------------------------- *)
open EcUtils
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
(* Parameter of the bdhoare abstract-procedure rule: the invariant, already
   typed. Nothing to resolve: the same record is the rule argument and the
   node payload. *)
type bdhoare_fun_abs = {
  bhfa_inv : ss_inv;   (* invariant I *)
}

type EcCoreGoal.rule += RBdHoareFunAbs of bdhoare_fun_abs

(* -------------------------------------------------------------------- *)
let bdhoareF_abs_spec (env : env) (f : EcPath.xpath) (inv : ss_inv) =
  let (top, _, oi, _) = EcLowPhlGoal.abstract_info env f in
  let fv = PV.fv env inv.m inv.inv in

  PV.check_depend env fv top;
  let ospec o =
    EcPlFun.check_oracle_use env top o;
    f_bdHoareF inv o inv FHge {m=inv.m;inv=f_r1} in

  let sg = List.map ospec (OI.allowed oi) in
  (inv, inv, EcPlFun.lossless_hyps env top f.x_sub :: sg)

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   procedure is abstract, the invariant does not depend on its globals, the
   oracles do not access them, the goal is [phoare [f : I ==> I] >= 1%r])
   are part of it, so the checker re-validates them. *)
let bdhoareF_abs_subgoals
    (hyps : LDecl.hyps) (bhf : bdHoareF) (n : bdhoare_fun_abs)
=
  if not (bhf.bhf_cmp = FHge && f_equal (bhf_bd bhf).inv f_r1) then
    failwith "bdhoareF-fun-abs: the bound is not [>= 1%r]";
  let pre, post, sg = bdhoareF_abs_spec (LDecl.toenv hyps) bhf.bhf_f n.bhfa_inv in
  if not (   EcReduction.ss_inv_alpha_eq hyps (bhf_pr bhf) pre
          && EcReduction.ss_inv_alpha_eq hyps (bhf_po bhf) post) then
    failwith "bdhoareF-fun-abs: the judgement is not [I ==> I]";
  sg

(* -------------------------------------------------------------------- *)
let bad_bound_ge tc = tc_error !!tc "bound must \">= 1%%r\""

(* Rule (TCB). *)
let t_bdhoareF_abs (r : bdhoare_fun_abs) (tc : tcenv1) =
  let bhf = tc1_as_bdhoareF tc in
  if not (bhf.bhf_cmp = FHge && f_equal (bhf_bd bhf).inv f_r1) then
    bad_bound_ge tc;
  FApi.xrule1 tc (RBdHoareFunAbs r)
    (bdhoareF_abs_subgoals (FApi.tc1_hyps tc) bhf r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareFunAbs n ->
         Some (EcPlRecheck.checker_of "bdhoareF-fun-abs" pf_as_bdhoareF
                 (fun hyps bhf -> bdhoareF_abs_subgoals hyps bhf n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): the consequence to [I ==> I], then the rule; an
   [= 1%r] goal goes through [>= 1%r] with the bound-changing consequence.

   TEMPORARY: the consequence rules still come from the not-yet-migrated
   [EcPhlConseq]. *)
let t_bdhoareF_abs_ge (r : bdhoare_fun_abs) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let bhf = tc1_as_bdhoareF tc in

  match bhf.bhf_cmp with
  | FHge when f_equal (bhf_bd bhf).inv f_r1 ->
      let pre, post, _ = bdhoareF_abs_spec env bhf.bhf_f r.bhfa_inv in
      FApi.t_last (t_bdhoareF_abs r)
        (EcPhlConseq.t_bdHoareF_conseq pre post tc)

  | _ -> bad_bound_ge tc

let t_bdhoareF_abs_full (r : bdhoare_fun_abs) (tc : tcenv1) =
  let bhf = tc1_as_bdhoareF tc in

  match bhf.bhf_cmp with
  | FHeq when f_equal (bhf_bd bhf).inv f_r1 ->
    let tc = FApi.t_seqsub (EcPhlConseq.t_bdHoareF_conseq_bd FHge (bhf_bd bhf)) [EcLowGoal.t_close EcLowGoal.t_trivial; t_bdhoareF_abs_ge r] tc in
    let pl_goal_count = FApi.tc_count tc - 3 in
    assert (pl_goal_count >= 0);
    FApi.t_lasts (EcPhlConseq.t_bdHoareF_conseq_bd FHeq (bhf_bd bhf) |- FApi.t_first (EcLowGoal.t_close EcLowGoal.t_trivial)) pl_goal_count tc
  | FHge when f_equal (bhf_bd bhf).inv f_r1 ->
      t_bdhoareF_abs_ge r tc
  | _ -> tc_error !!tc "bound must \"= 1%%r\" or \">= 1%%r\""

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [bdhoareF]. *)
let process_bdhoareF_abs (inv : pformula) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let m    = EcIdent.create "&hr" in
  let env' = LDecl.inv_memenv1 m hyps in
  let inv  = TTC.pf_process_form !!tc env' tbool inv in
  t_bdhoareF_abs_full { bhfa_inv = { inv; m; } } tc
