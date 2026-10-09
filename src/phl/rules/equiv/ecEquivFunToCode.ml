(* -------------------------------------------------------------------- *)
open EcTypes
open EcFol
open EcAst
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The equiv [fun-to-code] rule has no parameters. *)
type EcCoreGoal.rule += REquivFunToCode

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. The fresh variables are
   chosen deterministically from the memories of the goal. *)
let equivF_fun_to_code_subgoals (hyps : LDecl.hyps) (ef : equivF) : form list =
  let env = LDecl.toenv hyps in
  let ml, mr = ef.ef_ml, ef.ef_mr in
  let (fl,fr) = ef.ef_fl, ef.ef_fr in
  let (ml0, mlt), sl, rl, al = EcPlFun.to_code env fl ml in
  assert (EcIdent.id_equal ml0 ml);
  let (mr0, mrt), sr, rr, ar = EcPlFun.to_code env fr mr in
  assert (EcIdent.id_equal mr0 mr);
  let spr =
    let s = PVM.empty in
    let s = EcPlFun.add_var_tuple env pv_arg ml al ml s in
    let s = EcPlFun.add_var_tuple env pv_arg mr ar mr s in
    s in
  let spo =
    let s = PVM.empty in
    let s = EcPlFun.add_var env pv_res ml rl ml s in
    let s = EcPlFun.add_var env pv_res mr rr mr s in
    s in
  let pre   = PVM.subst env spr (ef_pr ef).inv in
  let post  = PVM.subst env spo (ef_po ef).inv in
  [f_equivS mlt mrt {ml;mr;inv=pre} sl sr {ml;mr;inv=post}]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_equivF_fun_to_code (tc : tcenv1) =
  let ef = tc1_as_equivF tc in
  FApi.xrule1 tc REquivFunToCode
    (equivF_fun_to_code_subgoals (FApi.tc1_hyps tc) ef)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivFunToCode ->
         Some (EcPlRecheck.checker_of "equivF-fun-to-code" pf_as_equivF
                 equivF_fun_to_code_subgoals)
     | _ -> None)
