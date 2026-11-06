(* -------------------------------------------------------------------- *)
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The rules deriving a probability-0 judgement from a hoare one have no
   parameters. *)
type EcCoreGoal.rule +=
  | RBdHoareSOfHoare
  | RBdHoareFOfHoare

(* -------------------------------------------------------------------- *)
(* The goal states that its postcondition has probability exactly 0. *)
let is_eq_zero (cmp : hoarecmp) (bd : ss_inv) =
  cmp = FHeq && f_equal bd.inv f_r0

(* Pure cores shared by the rules and their checkers. The side condition
   (the bound is [= 0%r]) is part of them, so the checker re-validates it. *)
let bdhoareS_of_hoare_subgoals (bhs : bdHoareS) : form list =
  if not (is_eq_zero bhs.bhs_cmp (bhs_bd bhs)) then
    failwith "bdhoareS-of-hoare: the bound is not = 0%r";
  let post = map_ss_inv1 f_not (bhs_po bhs) in
  [f_hoareS (snd bhs.bhs_m) (bhs_pr bhs) bhs.bhs_s
     { hsi_m = post.m; hsi_inv = POE.empty post.inv; }]

let bdhoareF_of_hoare_subgoals (bhf : bdHoareF) : form list =
  if not (is_eq_zero bhf.bhf_cmp (bhf_bd bhf)) then
    failwith "bdhoareF-of-hoare: the bound is not = 0%r";
  let post = map_ss_inv1 f_not (bhf_po bhf) in
  [f_hoareF (bhf_pr bhf) bhf.bhf_f
     { hsi_m = post.m; hsi_inv = POE.empty post.inv; }]

(* -------------------------------------------------------------------- *)
let not_eq_zero tc = tc_error !!tc "%s" "bound must be equal to 0%r"

(* Rules (TCB). *)
let t_bdhoareS_of_hoare (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  if not (is_eq_zero bhs.bhs_cmp (bhs_bd bhs)) then not_eq_zero tc;
  FApi.xrule1 tc RBdHoareSOfHoare (bdhoareS_of_hoare_subgoals bhs)

let t_bdhoareF_of_hoare (tc : tcenv1) =
  let bhf = tc1_as_bdhoareF tc in
  if not (is_eq_zero bhf.bhf_cmp (bhf_bd bhf)) then not_eq_zero tc;
  FApi.xrule1 tc RBdHoareFOfHoare (bdhoareF_of_hoare_subgoals bhf)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareSOfHoare ->
         Some (EcPlRecheck.checker_of "bdhoareS-of-hoare" pf_as_bdhoareS
                 (fun _hyps bhs -> bdhoareS_of_hoare_subgoals bhs))
     | RBdHoareFOfHoare ->
         Some (EcPlRecheck.checker_of "bdhoareF-of-hoare" pf_as_bdhoareF
                 (fun _hyps bhf -> bdhoareF_of_hoare_subgoals bhf))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): unless the bound already is [= 0%r], first
   turn the goal into [phoare [...] = 0%r] with the bound-changing
   consequence, try to close its side condition, then apply the rule.

   TEMPORARY: the bound-changing consequence still comes from the
   not-yet-migrated [EcPhlConseq]. *)
let t_bdhoareS_of_hoare_full (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  if is_eq_zero bhs.bhs_cmp (bhs_bd bhs) then t_bdhoareS_of_hoare tc else
    FApi.t_seqsub
      (EcPhlConseq.t_bdHoareS_conseq_bd FHeq { m = fst bhs.bhs_m; inv = f_r0; })
      [FApi.t_try EcPhlAuto.t_pl_trivial; t_bdhoareS_of_hoare]
      tc

let t_bdhoareF_of_hoare_full (tc : tcenv1) =
  let bhf = tc1_as_bdhoareF tc in
  if is_eq_zero bhf.bhf_cmp (bhf_bd bhf) then t_bdhoareF_of_hoare tc else
    FApi.t_seqsub
      (EcPhlConseq.t_bdHoareF_conseq_bd FHeq { m = bhf.bhf_m; inv = f_r0; })
      [FApi.t_try EcPhlAuto.t_pl_trivial; t_bdhoareF_of_hoare]
      tc
