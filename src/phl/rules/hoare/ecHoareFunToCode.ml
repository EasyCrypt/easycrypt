(* -------------------------------------------------------------------- *)
open EcTypes
open EcFol
open EcAst
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The hoare [fun-to-code] rule has no parameters. *)
type EcCoreGoal.rule += RHoareFunToCode

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. The fresh variables are
   chosen deterministically from the memory of the goal. *)
let hoareF_fun_to_code_subgoals (hyps : LDecl.hyps) (hf : sHoareF) : form list =
  let env = LDecl.toenv hyps in
  let f = hf.hf_f in
  let m = hf.hf_m in
  let (m0, mt), st, r, a = EcPlFun.to_code env f m in
  assert (EcIdent.id_equal m0 m);
  let spr = EcPlFun.add_var_tuple env pv_arg m a m PVM.empty in
  let spo = EcPlFun.add_var env pv_res m r m PVM.empty in
  let pre  = PVM.subst env spr (hf_pr hf).inv in
  let post = POE.map (PVM.subst env spo) (hf_po hf).hsi_inv in
  [f_hoareS mt {m;inv=pre} st {hsi_m=m;hsi_inv=post}]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_hoareF_fun_to_code (tc : tcenv1) =
  let hf = tc1_as_hoareF tc in
  FApi.xrule1 tc RHoareFunToCode
    (hoareF_fun_to_code_subgoals (FApi.tc1_hyps tc) hf)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareFunToCode ->
         Some (EcPlRecheck.checker_of "hoareF-fun-to-code" pf_as_hoareF
                 hoareF_fun_to_code_subgoals)
     | _ -> None)
