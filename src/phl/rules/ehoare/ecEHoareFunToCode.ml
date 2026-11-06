(* -------------------------------------------------------------------- *)
open EcTypes
open EcFol
open EcAst
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The ehoare [fun-to-code] rule has no parameters. *)
type EcCoreGoal.rule += REHoareFunToCode

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. The fresh variables are
   chosen deterministically from the memory of the goal. *)
let ehoareF_fun_to_code_subgoals (hyps : LDecl.hyps) (hf : eHoareF) : form list =
  let env = LDecl.toenv hyps in
  let f = hf.ehf_f in
  let m = hf.ehf_m in
  let (m0, mt), st, r, a = EcPlFun.to_code env f m in
  assert (EcIdent.id_equal m0 m);
  let spr = EcPlFun.add_var_tuple env pv_arg m a m PVM.empty in
  let spo = EcPlFun.add_var env pv_res m r m PVM.empty in
  let pre  = PVM.subst env spr (ehf_pr hf).inv in
  let post = PVM.subst env spo (ehf_po hf).inv in
  [f_eHoareS mt {m;inv=pre} st {m;inv=post}]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_ehoareF_fun_to_code (tc : tcenv1) =
  let hf = tc1_as_ehoareF tc in
  FApi.xrule1 tc REHoareFunToCode
    (ehoareF_fun_to_code_subgoals (FApi.tc1_hyps tc) hf)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareFunToCode ->
         Some (EcPlRecheck.checker_of "ehoareF-fun-to-code" pf_as_ehoareF
                 ehoareF_fun_to_code_subgoals)
     | _ -> None)
