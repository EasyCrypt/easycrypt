(* -------------------------------------------------------------------- *)
open EcTypes
open EcFol
open EcAst
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The bdhoare [fun-to-code] rule has no parameters. *)
type EcCoreGoal.rule += RBdHoareFunToCode

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. The fresh variables are
   chosen deterministically from the memory of the goal. *)
let bdhoareF_fun_to_code_subgoals (hyps : LDecl.hyps) (hf : bdHoareF) : form list =
  let env = LDecl.toenv hyps in
  let m = hf.bhf_m in
  let f = hf.bhf_f in
  let (m0, mt), st, r, a = EcPlFun.to_code env f m in
  assert (EcIdent.id_equal m0 m);
  let spr = EcPlFun.add_var_tuple env pv_arg m0 a m PVM.empty in
  let spo = EcPlFun.add_var env pv_res m0 r m PVM.empty in
  let pre  = PVM.subst env spr (bhf_pr hf).inv in
  let post = PVM.subst env spo (bhf_po hf).inv in
  let bd   = PVM.subst env spr (bhf_bd hf).inv in
  [f_bdHoareS mt {m;inv=pre} st {m;inv=post} hf.bhf_cmp {m;inv=bd}]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_bdhoareF_fun_to_code (tc : tcenv1) =
  let hf = tc1_as_bdhoareF tc in
  FApi.xrule1 tc RBdHoareFunToCode
    (bdhoareF_fun_to_code_subgoals (FApi.tc1_hyps tc) hf)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareFunToCode ->
         Some (EcPlRecheck.checker_of "bdhoareF-fun-to-code" pf_as_bdhoareF
                 bdhoareF_fun_to_code_subgoals)
     | _ -> None)
