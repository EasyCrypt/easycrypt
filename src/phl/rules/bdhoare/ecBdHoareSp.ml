(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the bdhoare [sp] rule as supplied by the caller: high
   level, the split position is still a symbolic code gap.

   Unlike the hoare and equiv [sp] rules, this rule is stated on [c1; c2]
   (it keeps an implicit [seq]): the bdhoare [seq] rule has extra premises
   that a derived composition cannot close without changing the visible
   goals (see the .mli). *)
type bdhoare_sp_rule = {
  bspr_at : EcMatching.Position.codegap1;   (* end of the sp-able prefix *)
}

(* Low-level parameters recorded in the proof-node: the split position is
   the RESOLVED integer index. *)
type bdhoare_sp_node = {
  bspn_at : EcMatching.Position.nm_codegap1;   (* resolved split index *)
}

type EcCoreGoal.rule += RBdHoareSp of bdhoare_sp_node

(* -------------------------------------------------------------------- *)
(* [true] when the bound is not written by [s]. *)
let bound_indep env (bhs : bdHoareS) (s : instr list) =
  let write = EcPV.s_write env (EcModules.stmt s) in
  let read  = EcPV.PV.fv env (fst bhs.bhs_m) (bhs_bd bhs).inv in
  EcPV.PV.indep env write read

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   prefix does not write the bound and is sp-able) are part of it, so the
   checker re-validates them. *)
let bdhoare_sp_subgoals
    (hyps : LDecl.hyps) (bhs : bdHoareS) (n : bdhoare_sp_node) : form list
=
  let env = LDecl.toenv hyps in
  let c1, c2 = EcMatching.Position.split_at_nmcgap1 n.bspn_at bhs.bhs_s in
  if not (bound_indep env bhs c1) then
    failwith "bdhoare-sp: the bound is written by the prefix";
  let rest, sp = EcPlSp.sp_stmt bhs.bhs_m env c1 (bhs_pr bhs).inv in
  if not (List.is_empty rest) then
    failwith "bdhoare-sp: the prefix is not sp-able";
  let pre = { m = fst bhs.bhs_m; inv = sp } in
  [f_bdHoareS (snd bhs.bhs_m) pre (stmt c2) (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs)]

(* -------------------------------------------------------------------- *)
(* Rule (TCB): resolve the code gap to an index, record the resolved node,
   and build its subgoal through the shared core. *)
let t_bdhoare_sp (r : bdhoare_sp_rule) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let bhs  = tc1_as_bdhoareS tc in
  let n    = { bspn_at = s_split_index (LDecl.toenv hyps) r.bspr_at bhs.bhs_s } in
  let subgoals =
    try  bdhoare_sp_subgoals hyps bhs n
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (RBdHoareSp n) subgoals

(* -------------------------------------------------------------------- *)
(* Checker: rerun ONLY the low-level core on the recorded index (see
   [EcPlRecheck]). *)
let () =
  register_rule_checker
    (function
     | RBdHoareSp n ->
         Some (EcPlRecheck.checker_of "bdhoare-sp" pf_as_bdhoareS
                 (fun hyps bhs -> bdhoare_sp_subgoals hyps bhs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): check, with the user-facing errors, that the
   bound is not written by the statement up to [at] and that sp gets that
   far, then apply the rule at the end of the longest sp-able prefix. *)
let t_bdhoare_sp_prefix (at : EcMatching.Position.codegap1 option) tc =
  let env = FApi.tc1_env tc in
  let bhs = tc1_as_bdhoareS tc in
  let c1, _ = o_split ~rev:true env at bhs.bhs_s in
  if not (bound_indep env bhs c1) then
    tc_error !!tc "the bound should not be modified by the statement \
                   targeted by [sp]";
  let rest, _ = EcPlSp.sp_stmt bhs.bhs_m env c1 (bhs_pr bhs).inv in
  EcPlSp.check_sp_progress tc (is_some at) rest;
  let k = List.length c1 - List.length rest in
  t_bdhoare_sp { bspr_at = EcPlSp.gap_at k } tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [bdHoareS], the position (if
   any) is a single one. *)
let process_bdhoare_sp (at : EcParsetree.pcodegap1 option) tc =
  let at = Option.map (EcTyping.trans_codegap1 (FApi.tc1_env tc)) at in
  t_bdhoare_sp_prefix at tc
