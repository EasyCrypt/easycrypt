open EcParsetree
open EcModules
open EcUnifyProc

open EcCoreGoal
open EcCoreGoal.FApi
open EcLowPhlGoal

(*---------------------------------------------------------------------------------------*)
(*
   This is transitivity star but allows for a range of code
   positions to select the program slice that is changing. The prefix and suffix are
   extracted and copied across to build the new program.
   This tactic fails if the new program cannot be shown equal to the old through the
   tactic chain `by inline; sim; auto=> />`.
*)

let t_outline_stmt side start_pos end_pos s tc =
  let env = FApi.tc1_env tc in
  let goal = tc1_as_equivS tc in

  (* Check which memory/program we are outlining *)
  let code = match side with
    | `Left  -> goal.es_sl
    | `Right -> goal.es_sr
  in

  (* Extract the program prefix and suffix *)
  let rest, code_suff  = s_split env end_pos code in
  let code_pref, _, _ = s_split_i env start_pos (stmt rest) in

  let new_prog = s_seq (s_seq (stmt code_pref) s) (stmt code_suff) in
  let tc = EcPhlTrans.t_equivS_trans_eq side new_prog tc in

  (* Solve the equivalence with the replaced code. *)
  let tp = match side with | `Left -> 1 | `Right -> 2 in
  let p = EcHiGoal.process_tfocus tc (Some [Some tp, Some tp], None) in
  let tc =
    t_onselect
      p
      (t_seqs [
        EcPhlInline.process_inline (`ByName (None, None, ([], None)));
        EcPhlEqobs.process_eqobs_in None {sim_pos = None; sim_hint = ([], None); sim_eqs = None};
        EcPhlAuto.t_auto;
        EcLowGoal.t_crush;
        EcHiGoal.process_done;
      ])
      tc
  in
  tc

(*---------------------------------------------------------------------------------------*)
(* The main tactic *)

(*
  `outline` - replace a program slice with a procedure call.

  Arguments,
    mode: dictates the method for function unification.
    side: selects the program (left or right) that will outlined.
    start_pos, end_pos: selects the particular slice of the program to outline.
    fname: path of the function that we are using to outline.
*)
let t_outline_proc (mode : [`Exact | `Alias]) side start_pos end_pos fname tc =
  let env = tc1_env tc in
  let goal = tc1_as_equivS tc in

  (* Get the code from the side we are outlining *)
  let code = match side with
    | `Left  -> goal.es_sl
    | `Right -> goal.es_sr
  in

  (* Get the exact code chunk we are outlining *)
  let code =
    let rest, ret, _ = s_split_i env end_pos code in
    if start_pos = end_pos then
      stmt [ret]
    else
      let _, hd, tl  = s_split_i env start_pos (stmt rest) in
      stmt (hd :: tl @ [ret])
  in

  (* Unify the function *)
  let proc_call = unify_func env mode fname code in

  (* Offload to transitivity *)
  t_outline_stmt side start_pos end_pos proc_call tc

(*---------------------------------------------------------------------------------------*)
(* Process a user call to outline *)

let process_outline info tc =
  let env = tc1_env tc in
  let side = info.outline_side in
  let goal = tc1_as_equivS tc in
  let ppe = EcPrinting.PPEnv.ofenv env in

  let start_pos =
    EcProofTyping.tc1_process_codepos1 tc
      (Some side, info.outline_start) in
  let end_pos =
    EcProofTyping.tc1_process_codepos1 tc
      (Some side, info.outline_end) in

  (* Check which memory we are outlining *)
  let mem = match side with
    | `Left  -> goal.es_ml
    | `Right -> goal.es_mr
  in

  try
    match info.outline_kind with
    | OKstmt s ->
      let s = EcProofTyping.tc1_process_stmt tc (EcMemory.memtype mem) s in
      t_outline_stmt side start_pos end_pos s tc
    | OKproc (f, alias) ->
      (* Get the function *)
      let f = EcTyping.trans_gamepath env f in
      let mode = if alias then `Alias else `Exact in
      t_outline_proc mode side start_pos end_pos f tc
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
