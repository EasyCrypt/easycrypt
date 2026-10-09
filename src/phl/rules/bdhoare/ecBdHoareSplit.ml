(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameters of the bdhoare [split] rules: the bounds of the premises.
   Already typed, nothing to resolve: the same records are the rule
   arguments and the node payloads. *)
type bdhoare_split_bop = {
  bsb_b1 : ss_inv;   (* bound for the left operand *)
  bsb_b2 : ss_inv;   (* bound for the right operand *)
  bsb_b3 : ss_inv;   (* opposite bound for the dual connective *)
}

type bdhoare_split_not = {
  bnt_b1 : ss_inv;   (* bound for [true] *)
  bnt_b2 : ss_inv;   (* opposite bound for the negated postcondition *)
}

type EcCoreGoal.rule +=
  | RBdHoareSSplitAnd of bdhoare_split_bop
  | RBdHoareFSplitAnd of bdhoare_split_bop
  | RBdHoareSSplitOr  of bdhoare_split_bop
  | RBdHoareFSplitOr  of bdhoare_split_bop
  | RBdHoareSSplitNot of bdhoare_split_not
  | RBdHoareFSplitNot of bdhoare_split_not

(* -------------------------------------------------------------------- *)
(* What the split rules read from a statement or procedure judgement:
   its memory, postcondition, comparison and bound, and how to restate it
   (same program and precondition) with another postcondition and bound. *)
type bdhoare_view = {
  bv_m   : memory;
  bv_po  : ss_inv;
  bv_cmp : hoarecmp;
  bv_bd  : ss_inv;
  bv_mk  : ss_inv -> hoarecmp -> ss_inv -> form;
}

let view_S (bhs : bdHoareS) = {
  bv_m   = fst bhs.bhs_m;
  bv_po  = bhs_po bhs;
  bv_cmp = bhs.bhs_cmp;
  bv_bd  = bhs_bd bhs;
  bv_mk  = (fun po cmp bd ->
    f_bdHoareS (snd bhs.bhs_m) (bhs_pr bhs) bhs.bhs_s po cmp bd);
}

let view_F (bhf : bdHoareF) = {
  bv_m   = bhf.bhf_m;
  bv_po  = bhf_po bhf;
  bv_cmp = bhf.bhf_cmp;
  bv_bd  = bhf_bd bhf;
  bv_mk  = (fun po cmp bd -> f_bdHoareF (bhf_pr bhf) bhf.bhf_f po cmp bd);
}

(* -------------------------------------------------------------------- *)
(* The two binary connectives, each with its dual. *)
type bop = [`And | `Or]

let bop_destr (op : bop) (po : ss_inv) =
  let destr = match op with `And -> destr_and | `Or -> destr_or in
  let f1, f2 = destr po.inv in
  ({ po with inv = f1 }, { po with inv = f2 })

let bop_dual (op : bop) =
  match op with `And -> map_ss_inv2 f_or | `Or -> map_ss_inv2 f_and

let bop_bound (b1 : ss_inv) (b2 : ss_inv) (b3 : ss_inv) =
  map_ss_inv2 f_real_sub (map_ss_inv2 f_real_add b1 b2) b3

(* Pure cores shared by the rules and their checkers. Their side
   conditions (the shape of the postcondition, the goal's bound being the
   combination of the premises' bounds, up to alpha-conversion) are part of
   them, so the checker re-validates them. *)
let split_bop_subgoals
    (op : bop) (hyps : LDecl.hyps) (v : bdhoare_view) (n : bdhoare_split_bop)
=
  let b1 = ss_inv_rebind n.bsb_b1 v.bv_m in
  let b2 = ss_inv_rebind n.bsb_b2 v.bv_m in
  let b3 = ss_inv_rebind n.bsb_b3 v.bv_m in
  let a, b = bop_destr op v.bv_po in
  if not (EcReduction.ss_inv_alpha_eq hyps (bop_bound b1 b2 b3) v.bv_bd) then
    failwith "bdhoare-split: the bound is not (b1 + b2) - b3";
  [ v.bv_mk a v.bv_cmp b1;
    v.bv_mk b v.bv_cmp b2;
    v.bv_mk (bop_dual op a b) (hoarecmp_opp v.bv_cmp) b3 ]

let split_not_subgoals
    (hyps : LDecl.hyps) (v : bdhoare_view) (n : bdhoare_split_not)
=
  let b1 = ss_inv_rebind n.bnt_b1 v.bv_m in
  let b2 = ss_inv_rebind n.bnt_b2 v.bv_m in
  if not (EcReduction.ss_inv_alpha_eq hyps (map_ss_inv2 f_real_sub b1 b2) v.bv_bd) then
    failwith "bdhoare-split-not: the bound is not b1 - b2";
  [ v.bv_mk (map_ss_inv1 (fun _ -> f_true) v.bv_po) v.bv_cmp b1;
    v.bv_mk (map_ss_inv1 f_not_simpl v.bv_po) (hoarecmp_opp v.bv_cmp) b2 ]

(* -------------------------------------------------------------------- *)
(* Rules (TCB). The side conditions are checked first, for the error
   messages. *)
let t_split_bop
    (op : bop) (mk : bdhoare_split_bop -> rule)
    (v : bdhoare_view) (r : bdhoare_split_bop) (tc : tcenv1)
=
  let hyps = FApi.tc1_hyps tc in
  (try ignore (bop_destr op v.bv_po) with DestrError _ ->
     tc_error !!tc "the postcondition must be a %s"
       (match op with `And -> "conjunction" | `Or -> "disjunction"));
  let b1 = ss_inv_rebind r.bsb_b1 v.bv_m in
  let b2 = ss_inv_rebind r.bsb_b2 v.bv_m in
  let b3 = ss_inv_rebind r.bsb_b3 v.bv_m in
  if not (EcReduction.ss_inv_alpha_eq hyps (bop_bound b1 b2 b3) v.bv_bd) then
    tc_error !!tc "the bound must be of the form (b1 + b2) - b3";
  FApi.xrule1 tc (mk r) (split_bop_subgoals op hyps v r)

let t_bdhoareS_split_and r tc =
  t_split_bop `And (fun n -> RBdHoareSSplitAnd n) (view_S (tc1_as_bdhoareS tc)) r tc
let t_bdhoareF_split_and r tc =
  t_split_bop `And (fun n -> RBdHoareFSplitAnd n) (view_F (tc1_as_bdhoareF tc)) r tc
let t_bdhoareS_split_or r tc =
  t_split_bop `Or (fun n -> RBdHoareSSplitOr n) (view_S (tc1_as_bdhoareS tc)) r tc
let t_bdhoareF_split_or r tc =
  t_split_bop `Or (fun n -> RBdHoareFSplitOr n) (view_F (tc1_as_bdhoareF tc)) r tc

let t_split_not
    (mk : bdhoare_split_not -> rule)
    (v : bdhoare_view) (r : bdhoare_split_not) (tc : tcenv1)
=
  let hyps = FApi.tc1_hyps tc in
  let b1 = ss_inv_rebind r.bnt_b1 v.bv_m in
  let b2 = ss_inv_rebind r.bnt_b2 v.bv_m in
  if not (EcReduction.ss_inv_alpha_eq hyps (map_ss_inv2 f_real_sub b1 b2) v.bv_bd) then
    tc_error !!tc "the bound must be of the form b1 - b2";
  FApi.xrule1 tc (mk r) (split_not_subgoals hyps v r)

let t_bdhoareS_split_not r tc =
  t_split_not (fun n -> RBdHoareSSplitNot n) (view_S (tc1_as_bdhoareS tc)) r tc
let t_bdhoareF_split_not r tc =
  t_split_not (fun n -> RBdHoareFSplitNot n) (view_F (tc1_as_bdhoareF tc)) r tc

(* -------------------------------------------------------------------- *)
let () =
  let bop name op destr view n =
    EcPlRecheck.checker_of name destr
      (fun hyps j -> split_bop_subgoals op hyps (view j) n) in
  let not_ name destr view n =
    EcPlRecheck.checker_of name destr
      (fun hyps j -> split_not_subgoals hyps (view j) n) in
  register_rule_checker
    (function
     | RBdHoareSSplitAnd n ->
         Some (bop "bdhoareS-split-and" `And pf_as_bdhoareS view_S n)
     | RBdHoareFSplitAnd n ->
         Some (bop "bdhoareF-split-and" `And pf_as_bdhoareF view_F n)
     | RBdHoareSSplitOr n ->
         Some (bop "bdhoareS-split-or" `Or pf_as_bdhoareS view_S n)
     | RBdHoareFSplitOr n ->
         Some (bop "bdhoareF-split-or" `Or pf_as_bdhoareF view_F n)
     | RBdHoareSSplitNot n ->
         Some (not_ "bdhoareS-split-not" pf_as_bdhoareS view_S n)
     | RBdHoareFSplitNot n ->
         Some (not_ "bdhoareF-split-not" pf_as_bdhoareF view_F n)
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): unless the goal's bound already is the
   combination of the given bounds, first change it into that combination
   with the bound-changing consequence (its side condition is left open),
   then apply the rule.

   TEMPORARY: the bound-changing consequence still comes from the
   not-yet-migrated [EcPhlConseq]. *)
let not_bdhoare tc =
  tc_error !!tc "the conclusion should be a bdhoare judgment"

let t_with_bound ~(same : ss_inv -> ss_inv -> bool) nb tS tF (tc : tcenv1) =
  let with_bound t_conseq_bd t_main (v : bdhoare_view) =
    if   same nb v.bv_bd
    then t_main tc
    else FApi.t_seqsub (t_conseq_bd v.bv_cmp nb) [t_id; t_main] tc
  in
  match (FApi.tc1_goal tc).f_node with
  | FbdHoareS bhs -> with_bound EcPhlConseq.t_bdHoareS_conseq_bd tS (view_S bhs)
  | FbdHoareF bhf -> with_bound EcPhlConseq.t_bdHoareF_conseq_bd tF (view_F bhf)
  | _ -> not_bdhoare tc

let t_bdhoare_split_and (r : bdhoare_split_bop) =
  t_with_bound ~same:(fun nb bd -> f_equal nb.inv bd.inv)
    (bop_bound r.bsb_b1 r.bsb_b2 r.bsb_b3)
    (t_bdhoareS_split_and r) (t_bdhoareF_split_and r)

let t_bdhoare_split_or (r : bdhoare_split_bop) =
  t_with_bound ~same:(fun nb bd -> f_equal nb.inv bd.inv)
    (bop_bound r.bsb_b1 r.bsb_b2 r.bsb_b3)
    (t_bdhoareS_split_or r) (t_bdhoareF_split_or r)

let t_bdhoare_split_not (r : bdhoare_split_not) (tc : tcenv1) =
  t_with_bound ~same:(EcReduction.ss_inv_alpha_eq (FApi.tc1_hyps tc))
    (map_ss_inv2 f_real_sub r.bnt_b1 r.bnt_b2)
    (t_bdhoareS_split_not r) (t_bdhoareF_split_not r) tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is expected to be a bdhoare judgement. Type the
   bounds in its memory, then apply the derived split tactic matching the
   surface form. *)
let process_bdhoare_split (info : EcParsetree.bdh_split) (tc : tcenv1) =
  let _, concl = FApi.tc1_flat tc in

  let pr, po =
    match concl.f_node with
    | FbdHoareS bhs -> (bhs_pr bhs, bhs_po bhs)
    | FbdHoareF bhf -> (bhf_pr bhf, bhf_po bhf)
    | _ -> tc_error !!tc "the conclusion must be a bdhoare judgment" in

  match info with
  | EcParsetree.BDH_split_bop (b1, b2, b3) ->
      let t =
             if is_and po.inv then t_bdhoare_split_and
        else if is_or  po.inv then t_bdhoare_split_or
        else
          tc_error !!tc
            "the postcondition must be a conjunction or a disjunction"
      in
      let _, b1 = TTC.tc1_process_Xhl_form tc treal b1 in
      let _, b2 = TTC.tc1_process_Xhl_form tc treal b2 in
      let b3 =
        b3 |> omap (fun f -> snd (TTC.tc1_process_Xhl_form tc treal f))
           |> odfl { m = b1.m; inv = f_r0; } in

      t { bsb_b1 = b1; bsb_b2 = b2; bsb_b3 = b3; } tc

  | EcParsetree.BDH_split_or_case (b1, b2, f) ->
      let _, b1 = TTC.tc1_process_Xhl_form tc treal b1 in
      let _, b2 = TTC.tc1_process_Xhl_form tc treal b2 in
      let _, f  = TTC.tc1_process_Xhl_formula tc f in

      (* TEMPORARY: the consequence rule still comes from the
         not-yet-migrated [EcPhlConseq]. *)
      let t_conseq po lemma tactic =
        let rwtt tc =
          let pt = ptglobal ~tys:[] lemma in

          let rwtt = [
            EcLowGoal.t_intros_i [EcIdent.create "_"];
            EcHiGoal.LowRewrite.t_rewrite (`LtoR, None, None) pt;
            t_true;
          ] in FApi.t_seqs rwtt tc
        in

        FApi.t_seqsub
          (EcPhlConseq.t_conseq (Inv_ss pr) (Inv_ss po))
          [t_true; rwtt; tactic]
      in

      t_conseq
        (map_ss_inv2 f_or
           (map_ss_inv2 f_and f po)
           (map_ss_inv2 f_and (map_ss_inv1 f_not f) po))
        (EcCoreLib.CI_Logic.mk_logic "orDandN")
        (FApi.t_on1seq 3
           (t_bdhoare_split_or
              { bsb_b1 = b1; bsb_b2 = b2; bsb_b3 = { m = b1.m; inv = f_r0; } })
           (t_conseq
              { inv = f_false; m = b1.m; }
              (EcCoreLib.CI_Logic.mk_logic "andDorN")
              EcHiGoal.process_trivial))
        tc

  | EcParsetree.BDH_split_not (b1, b2) ->
      let _, b2 = TTC.tc1_process_Xhl_form tc treal b2 in
      let b1 =
        b1 |> omap (fun f -> snd (TTC.tc1_process_Xhl_form tc treal f))
           |> odfl { m = b2.m; inv = f_r1; } in
      t_bdhoare_split_not { bnt_b1 = b1; bnt_b2 = b2; } tc
