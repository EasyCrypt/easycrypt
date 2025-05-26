open EcParsetree
open EcModules
open EcUnifyProc

open EcCoreGoal
open EcCoreGoal.FApi
open EcLowPhlGoal

(*---------------------------------------------------------------------------------------*)

(* `by inline; sim; auto=> />` *)
let t_auto_equiv_sim =
  t_seqs [
    EcPhlInline.process_inline (`ByName (None, None, ([], None)));
    EcPhlEqobs.process_eqobs_in None {sim_pos = None; sim_hint = ([], None); sim_eqs = None};
    EcPhlAuto.t_auto;
    EcLowGoal.t_crush;
    EcHiGoal.process_done;
    ]

(*---------------------------------------------------------------------------------------*)
(* The main tactic *)

type outline_variant =
  | OV_Proc of [`Exact | `Alias] * EcPath.xpath
  | OV_Stmt of stmt

let t_outline side cpr variant tc =
  let env = tc1_env tc in
  let goal = tc1_as_equivS tc in

  (* Get the code from the side we are outlining *)
  let code = match side with
    | `Left  -> goal.es_sl
    | `Right -> goal.es_sr
  in

  let doit env si =
    match variant with
    | OV_Proc (mode, f) -> (unify_func env mode f (stmt si)).s_node
    | OV_Stmt s -> s.s_node
  in
  let new_prog = EcMatching.Zipper.map_range env cpr doit code in

  (* Offload to transitivity *)
  let tc = EcPhlTrans.t_equivS_trans_eq side new_prog tc in

  (* Solve the equivalence with the replaced code. *)
  let tp = match side with | `Left -> 1 | `Right -> 2 in
  let p = EcHiGoal.process_tfocus tc (Some [Some tp, Some tp], None) in
  t_onselect p t_auto_equiv_sim tc

(*---------------------------------------------------------------------------------------*)
(* Process a user call to outline *)

let process_outline info tc =
  let env = tc1_env tc in
  let side = info.outline_side in
  let goal = tc1_as_equivS tc in
  let ppe = EcPrinting.PPEnv.ofenv env in

  let range =
    EcProofTyping.tc1_process_codepos_range tc
      (Some side, info.outline_range) in

  (* Check which memory we are outlining *)
  let mem = match side with
    | `Left  -> goal.es_ml
    | `Right -> goal.es_mr
  in

  try
    match info.outline_kind with
    | OKstmt s ->
      let s = EcProofTyping.tc1_process_stmt tc (EcMemory.memtype mem) s in
      t_outline side range (OV_Stmt s) tc
    | OKproc (f, alias) ->
      (* Get the function *)
      let f = EcTyping.trans_gamepath env f in
      let mode = if alias then `Alias else `Exact in
      t_outline side range (OV_Proc (mode, f)) tc
  with
  | UnificationError (UE_UnificationFailArg x) ->
     tc_error !!tc "Outline: unable to unify arg `%s`." x
  | UnificationError (UE_UnificationFailPv x) ->
     tc_error !!tc "Outline: unable to unify variable `%s`." x
  | UnificationError UE_AbstractFun ->
     tc_error !!tc "Outline: cannot unify abstract function."
  | UnificationError UE_AliasNoRet ->
     tc_error !!tc "Outline: cannot alias unit returning function. To use the aliasing mode, the function must return a program variable or a tuple of program variables."
  | UnificationError UE_AliasNotPv ->
     tc_error !!tc "Outline: cannot alias function which does not just return program variables. To use the aliasing mode, the function must return a program variable or a tuple of program variables."
  | UnificationError (UE_TypeMismatch (e1, e2)) ->
      tc_error !!tc "Outline: cannot unify expressions @[<hov>`%a`@ and `%a`@] they have different types @[`%a`@ <> `%a`@]."
        (EcPrinting.pp_expr ppe) e1 (EcPrinting.pp_expr ppe) e2
        (EcPrinting.pp_type ppe) e1.e_ty (EcPrinting.pp_type ppe) e2.e_ty
  | UnificationError UE_InvalidRetInstr ->
     tc_error !!tc "Outline: return instruction must be an assign. Perhaps consider using the alias variant using `~`."
  | UnificationError (UE_DifferentProgramLengths (s1, s2)) ->
     tc_error !!tc "Outline: body's are different lengths\n%a ~ %a." (EcPrinting.pp_stmt ppe) s1 (EcPrinting.pp_stmt ppe) s2
  | UnificationError (UE_InstrNotInLockstep (i1, i2))->
     tc_error !!tc "outline: instructions not in sync\n%a ~ %a." (EcPrinting.pp_instr ppe) i1 (EcPrinting.pp_instr ppe) i2
  | UnificationError (UE_LvNotInLockstep (_lv1, _lv2))->
     tc_error !!tc "Outline: left values not in sync\n."
  | UnificationError (UE_ExprNotInLockstep (e1, e2))->
     tc_error !!tc "Outline: expressions not in sync\n%a ~ %a." (EcPrinting.pp_expr ppe) e1 (EcPrinting.pp_expr ppe) e2
