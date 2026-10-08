(* -------------------------------------------------------------------- *)
open EcTypes
open EcFol
open EcAst
open EcModules
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The eager [fun-to-code] rule has no parameters. *)
type EcCoreGoal.rule += REagerFunToCode

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. The fresh variables are
   chosen deterministically from the memories of the goal. *)
let eagerF_fun_to_code_subgoals (hyps : LDecl.hyps) (eg : eagerF) : form list =
  let env = LDecl.toenv hyps in
  let ml, mr = eg.eg_ml, eg.eg_mr in
  let (fl,fr) = eg.eg_fl, eg.eg_fr in
  let (ml0, mlt), sl, rl, al = EcPlFun.to_code env fl ml in
  assert (EcIdent.id_equal ml0 ml);
  let (mr0, mrt), sr, rr, ar = EcPlFun.to_code env fr mr in
  assert (EcIdent.id_equal mr0 mr);
  let spr =
    let s = PVM.empty in
    let s = EcPlFun.add_var_tuple env pv_arg ml0 al ml s in
    let s = EcPlFun.add_var_tuple env pv_arg mr0 ar mr s in
    s in
  let spo =
    let s = PVM.empty in
    let s = EcPlFun.add_var env pv_res ml0 rl ml s in
    let s = EcPlFun.add_var env pv_res mr0 rr mr s in
    s in
  let pre   = PVM.subst env spr (eg_pr eg).inv in
  let post  = PVM.subst env spo (eg_po eg).inv in
  [f_equivS mlt mrt {ml;mr;inv=pre} (s_seq eg.eg_sl sl) (s_seq sr eg.eg_sr) {ml;mr;inv=post}]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_eagerF_fun_to_code (tc : tcenv1) =
  let eg = tc1_as_eagerF tc in
  FApi.xrule1 tc REagerFunToCode
    (eagerF_fun_to_code_subgoals (FApi.tc1_hyps tc) eg)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REagerFunToCode ->
         Some (EcPlRecheck.checker_of "eagerF-fun-to-code" pf_as_eagerF
                 eagerF_fun_to_code_subgoals)
     | _ -> None)
