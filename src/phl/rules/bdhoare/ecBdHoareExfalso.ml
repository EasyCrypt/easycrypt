(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The bdhoare [exfalso] rules have no parameters. *)
type EcCoreGoal.rule +=
  | RBdHoareSExfalso
  | RBdHoareFExfalso

(* -------------------------------------------------------------------- *)
(* Pure cores shared by the rules and their checkers. The side condition
   (the precondition is syntactically [false]) is part of them, so the
   checker re-validates it. *)
let bdhoareS_exfalso_subgoals (bhs : bdHoareS) : form list =
  if not (f_equal (bhs_pr bhs).inv f_false) then
    failwith "bdhoareS-exfalso: the precondition is not false";
  [EcSubst.f_forall_mems_ss_inv bhs.bhs_m
     (map_ss_inv1 (f_real_le f_r0) (bhs_bd bhs))]

let bdhoareF_exfalso_subgoals (hyps : LDecl.hyps) (bhf : bdHoareF) : form list =
  if not (f_equal (bhf_pr bhf).inv f_false) then
    failwith "bdhoareF-exfalso: the precondition is not false";
  let me, _ = Fun.hoareF_memenv bhf.bhf_m bhf.bhf_f (LDecl.toenv hyps) in
  [EcSubst.f_forall_mems_ss_inv me
     (map_ss_inv1 (f_real_le f_r0) (bhf_bd bhf))]

(* -------------------------------------------------------------------- *)
let not_false tc = tc_error !!tc "pre-condition is not `false'"

(* Rules (TCB). *)
let t_bdhoareS_exfalso (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  if not (f_equal (bhs_pr bhs).inv f_false) then not_false tc;
  FApi.xrule1 tc RBdHoareSExfalso (bdhoareS_exfalso_subgoals bhs)

let t_bdhoareF_exfalso (tc : tcenv1) =
  let bhf = tc1_as_bdhoareF tc in
  if not (f_equal (bhf_pr bhf).inv f_false) then not_false tc;
  FApi.xrule1 tc RBdHoareFExfalso
    (bdhoareF_exfalso_subgoals (FApi.tc1_hyps tc) bhf)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareSExfalso ->
         Some (EcPlRecheck.checker_of "bdhoareS-exfalso" pf_as_bdhoareS
                 (fun _hyps bhs -> bdhoareS_exfalso_subgoals bhs))
     | RBdHoareFExfalso ->
         Some (EcPlRecheck.checker_of "bdhoareF-exfalso" pf_as_bdhoareF
                 (fun hyps bhf -> bdhoareF_exfalso_subgoals hyps bhf))
     | _ -> None)
