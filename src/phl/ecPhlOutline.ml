open EcParsetree
open EcFol
open EcUtils
open EcModules
open EcTypes
open EcSymbols
open EcUnifyProc

open EcCoreGoal
open EcCoreGoal.FApi
open EcLowPhlGoal

(*---------------------------------------------------------------------------------------*)
(*
   This is the improved transitivity star from above but allows for a range of code
   positions to select the program slice that is changing. The prefix and suffix are
   extracted and copied across to build the new program.
*)
(* FIXME: Maybe move to ecPhlTrans as well *)

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

  (* The middle goal, showing equivalence with the replaced code, ideally solves. *)
  let tp = match side with | `Left -> 1 | `Right -> 2 in
  let p = EcHiGoal.process_tfocus tc (Some [Some tp, Some tp], None) in
  let tc =
    t_onselect
      p
      (t_try (
           t_seqs [
               EcPhlInline.process_inline (`ByName (None, None, ([], None)));
               EcPhlEqobs.process_eqobs_in none {sim_pos = none; sim_hint = ([], none); sim_eqs = none};
               EcPhlAuto.t_auto;
               EcHiGoal.process_done;
         ]))
      tc
  in
  tc

(*---------------------------------------------------------------------------------------*)
(* The main tactic *)

type out_error =
  | OE_InvalidFunc
  | OE_UnnecessaryReturn
  | OE_UnificationFailure of EcSymbols.symbol

exception OutlineError of out_error

(*
  `outline` - replace a program slice with a procedure call.

  Arguments,
    side: selects the program (left or right) that will outlined.
    start_pos, end_pos: selects the particular slice of the program to outline.
    fname: path of the function that we are using to outline.
    res_lv: optional left-value for the result.
      when None, assume the entire slice contains the body and return.
      otherwise, assume entire slice contains just the body.
*)
let t_outline_proc side start_pos end_pos fname res_lv tc =
  let env = tc1_env tc in
  let goal = tc1_as_equivS tc in

  (* Extract the function args, body, and return expression *)
  let func = EcEnv.Fun.by_xpath fname env in
  let f_def =
    match func.f_def with
    | FBdef d -> d
    | _ -> raise (OutlineError OE_InvalidFunc)
  in

  (* Get the code from the side we are outlining *)
  let code = match side with
    | `Left  -> goal.es_sl
    | `Right -> goal.es_sr
  in

  (* Get the return statement and body we will attempt to unify *)
  let old_code_body, old_code_ret =
    let rest, ret_instr, _ = s_split_i env end_pos code in
    let body =
       if start_pos = end_pos then
         s_empty
       else
         let _, hd, tl  = s_split_i env start_pos (stmt rest) in
         stmt (hd :: tl)
    in

    match f_def.f_ret, res_lv with
    | None, None ->
       s_seq body (stmt [ret_instr]), None
    | Some _, Some _ ->
       s_seq body (stmt [ret_instr]), None
    | Some _, None ->
       body, Some ret_instr
    | _, _ -> raise (OutlineError OE_UnnecessaryReturn)
  in

  (* Get the symbol for each function argument used *)
  let arg_names = func.f_sig.fs_anames in
  let args = List.filter_map ov_name arg_names in

  (* Insert all the argument symbols we are attempting to unify *)
  let umap = List.fold_left (fun umap a -> Msym.add a Empty umap) Msym.empty args in

  (* Unify the function *)
  let lv, args_map = unify_func umap f_def old_code_body old_code_ret in
  (* Use the correct lv *)
  let lv = match lv with | None -> res_lv | _ -> lv in

  (* Check that we were able to unify all arguments *)
  let args =
    List.map
      (fun a ->
        match Msym.find a args_map with
        | Empty -> raise (OutlineError (OE_UnificationFailure a))
        | Fixed e -> e
      )
      args
  in

  (* Buid the call statement *)
  let proc_call = s_call (lv, fname, args) in

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
    | OKproc (f, pres_lv) ->
       let loc = EcLocation.loc f in
       (* Get the function *)
       let f = EcTyping.trans_gamepath env f in
       let func = EcEnv.Fun.by_xpath f env in
       let f_def =
         match func.f_def with
         | FBdef d -> d
         | _ -> raise (OutlineError OE_InvalidFunc)
       in

       (* Translate the res_lv if given *)
       let res_lv =
         match pres_lv, f_def.f_ret with
         | Some r, Some e -> begin
             try
               let subenv = EcEnv.Memory.push_active mem env in
               let ue = EcUnify.UniEnv.create (Some []) in
               let res = EcTyping.transexpcast subenv `InProc ue e.e_ty r in
               let tu = EcUnify.UniEnv.close ue in
               let sty = f_subst_init ~tu () in
               let es = e_subst sty in
               Some (lv_of_expr (es res))
             with EcUnify.UninstanciateUni ->
               EcTyping.tyerror loc env EcTyping.FreeTypeVariables
           end
         | None, _ -> None
         | _, _ -> raise (OutlineError OE_UnnecessaryReturn)
       in

       t_outline_proc side start_pos end_pos f res_lv tc
  with
  | OutlineError OE_UnnecessaryReturn ->
     tc_error !!tc "outline: left-value given when function does not return"
  | OutlineError OE_InvalidFunc ->
     tc_error !!tc "outline: cannot outline an abstract function"
  | OutlineError (OE_UnificationFailure x) ->
     tc_error !!tc "outline: unable to unify `%s`" x
  | UnificationError UE_InvalidRetInstr ->
     tc_error !!tc ("outline: return instruction kind not supported")
  | UnificationError (UE_DifferentProgramLengths (s1, s2)) ->
     tc_error !!tc "outline: body's are different lengths\n%a ~ %a" (EcPrinting.pp_stmt ppe) s1 (EcPrinting.pp_stmt ppe) s2
  | UnificationError (UE_InstrNotInLockstep (i1, i2))->
     tc_error !!tc "outline: instructions not in sync\n%a ~ %a" (EcPrinting.pp_instr ppe) i1 (EcPrinting.pp_instr ppe) i2
  | UnificationError (UE_ExprNotInLockstep (e1, e2))->
     tc_error !!tc "outline: expressions not in sync\n%a ~ %a" (EcPrinting.pp_expr ppe) e1 (EcPrinting.pp_expr ppe) e2
