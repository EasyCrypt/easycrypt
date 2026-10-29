(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The bdhoare [prbounded] rules have no parameters. *)
type EcCoreGoal.rule +=
  | RBdHoareSPrBounded
  | RBdHoareFPrBounded

(* -------------------------------------------------------------------- *)
(* The judgement holds for every program: a probability is at most [1%r],
   at least [0%r], and is [0%r] for the [false] event. *)
let is_trivial (cmp : hoarecmp) (po : ss_inv) (bd : ss_inv) =
  match cmp with
  | FHle when f_equal bd.inv f_r1 -> true
  | FHge when f_equal bd.inv f_r0 -> true
  | _ -> f_equal po.inv f_false && f_equal bd.inv f_r0

(* Pure core shared by the rules and their checkers, over the memory [m]
   the premise quantifies over. Its side condition (the judgement is
   trivial, or the comparison is [<=] or [>=]) is part of it, so the
   checker re-validates it. *)
let prbounded_subgoals
    (m : memenv) (pr : ss_inv) (po : ss_inv) (cmp : hoarecmp) (bd : ss_inv)
=
  let one  = { m = fst m; inv = f_r1; } in
  let zero = { m = fst m; inv = f_r0; } in
  if is_trivial cmp po bd then [] else
    match cmp with
    | FHle ->
        [EcSubst.f_forall_mems_ss_inv m
           (map_ss_inv2 f_imp pr (map_ss_inv2 f_real_le one bd))]
    | FHge ->
        [EcSubst.f_forall_mems_ss_inv m
           (map_ss_inv2 f_imp pr (map_ss_inv2 f_real_le bd zero))]
    | FHeq ->
        failwith "bdhoare-prbounded: non-trivial judgement with = bound"

let bdhoareS_prbounded_subgoals (bhs : bdHoareS) : form list =
  prbounded_subgoals bhs.bhs_m (bhs_pr bhs) (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs)

let bdhoareF_prbounded_subgoals (hyps : LDecl.hyps) (bhf : bdHoareF) =
  let m = fst (Fun.hoareF_memenv bhf.bhf_m bhf.bhf_f (LDecl.toenv hyps)) in
  prbounded_subgoals m (bhf_pr bhf) (bhf_po bhf) bhf.bhf_cmp (bhf_bd bhf)

(* -------------------------------------------------------------------- *)
(* The rule applies to a non-trivial judgement only when the caller allows
   a premise ([conseq]), and never to an [=] one. *)
let check_applies tc ~conseq cmp po bd =
  if not (is_trivial cmp po bd || (conseq && cmp <> FHeq)) then
    tc_error !!tc "cannot solve the probabilistic judgement"

(* Rules (TCB). *)
let t_bdhoareS_prbounded ~(conseq : bool) (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  check_applies tc ~conseq bhs.bhs_cmp (bhs_po bhs) (bhs_bd bhs);
  FApi.xrule1 tc RBdHoareSPrBounded (bdhoareS_prbounded_subgoals bhs)

let t_bdhoareF_prbounded ~(conseq : bool) (tc : tcenv1) =
  let bhf = tc1_as_bdhoareF tc in
  check_applies tc ~conseq bhf.bhf_cmp (bhf_po bhf) (bhf_bd bhf);
  FApi.xrule1 tc RBdHoareFPrBounded
    (bdhoareF_prbounded_subgoals (FApi.tc1_hyps tc) bhf)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareSPrBounded ->
         Some (EcPlRecheck.checker_of "bdhoareS-prbounded" pf_as_bdhoareS
                 (fun _hyps bhs -> bdhoareS_prbounded_subgoals bhs))
     | RBdHoareFPrBounded ->
         Some (EcPlRecheck.checker_of "bdhoareF-prbounded" pf_as_bdhoareF
                 (fun hyps bhf -> bdhoareF_prbounded_subgoals hyps bhf))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Dispatcher (no node of its own). *)
let t_bdhoare_prbounded ~(conseq : bool) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FbdHoareF _ -> t_bdhoareF_prbounded ~conseq tc
  | FbdHoareS _ -> t_bdhoareS_prbounded ~conseq tc
  | _ -> tc_error_noXhl ~kinds:[`PHoare `Any] !!tc
