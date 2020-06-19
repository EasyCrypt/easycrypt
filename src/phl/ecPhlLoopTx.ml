(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcReduction
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal
open EcPhlRCond
open EcLowGoal

module Zpr = EcMatching.Zipper
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
type fission_t    = oside * codepos * (int * (int * int))
type fusion_t     = oside * codepos * (int * (int * int))
type unroll_t     = oside * codepos * bool
type splitwhile_t = pexpr * oside * codepos

(* -------------------------------------------------------------------- *)
let check_independence (pf, hyps) b init c1 c2 c3 =
  let env = LDecl.toenv hyps in

  (* TODO improve error message, see swap *)
  let check_disjoint s1 s2 =
    if not (PV.indep env s1 s2) then
      tc_error pf "independence check failed"
  in

  let fv_b    = e_read   env b    in
  let rd_init = is_read  env init in
  let wr_init = is_write env init in
  let rd_c1   = is_read  env c1   in
  let rd_c2   = is_read  env c2   in
  let rd_c3   = is_read  env c3   in
  let wr_c1   = is_write env c1   in
  let wr_c2   = is_write env c2   in
  let wr_c3   = is_write env c3   in

  check_disjoint rd_c1 wr_c2;
  check_disjoint rd_c2 wr_c1;
  List.iter (check_disjoint fv_b) [wr_c1; wr_c2];
  check_disjoint fv_b (PV.diff wr_c3 wr_init);
  List.iter (check_disjoint rd_init) [wr_init; wr_c1; wr_c3];
  List.iter (check_disjoint rd_c3) [wr_c1; wr_c2]

(* -------------------------------------------------------------------- *)
let fission_stmt (il, (d1, d2)) (pf, hyps) me zpr =
  if d2 < d1 then
    tc_error pf "%s, %s"
      "in loop-fission"
      "second break offset must not be lower than the first one";

  let (hd, init, b, sw, tl) =
    match zpr.Zpr.z_tail with
    | { i_node = Swhile (b, sw) } :: tl -> begin
        if List.length zpr.Zpr.z_head < il then
          tc_error pf "while-loop is not headed by %d intructions" il;
      let (init, hd) = List.takedrop il zpr.Zpr.z_head in
        (hd, init, b, sw, tl)
      end
    | _ -> tc_error pf "code position does not lead to a while-loop"
  in

  if d2 > List.length sw.s_node then
    tc_error pf "in loop fission, invalid offsets range";

  let (s1, s2, s3) =
    let (s1, s2) = List.takedrop (d1   ) sw.s_node in
    let (s2, s3) = List.takedrop (d2-d1) s2 in
      (s1, s2, s3)
  in

  check_independence (pf, hyps) b init s1 s2 s3;

  let wl1 = i_while (b, stmt (s1 @ s3)) in
  let wl2 = i_while (b, stmt (s2 @ s3)) in
  let fis =   (List.rev_append init [wl1])
            @ (List.rev_append init [wl2]) in

    (me, { zpr with Zpr.z_head = hd; Zpr.z_tail = fis @ tl }, [])

let t_fission_r side cpos infos g =
  let tr = fun side -> `LoopFission (side, cpos, infos) in
  let cb = fun cenv _ me zpr -> fission_stmt infos cenv me zpr in
  t_code_transform side
    ~bdhoare:true ~choare:None
    cpos tr (t_zip cb) g

let t_fission = FApi.t_low3 "loop-fission" t_fission_r

(* -------------------------------------------------------------------- *)
let fusion_stmt (il, (d1, d2)) (pf, hyps) me zpr =
  let env = LDecl.toenv hyps in

  let (hd, init1, b1, sw1, tl) =
    match zpr.Zpr.z_tail with
    | { i_node = Swhile (b, sw) } :: tl -> begin
        if List.length zpr.Zpr.z_head < il then
          tc_error pf "1st while-loop is not headed by %d intruction(s)" il;
      let (init, hd) = List.takedrop il zpr.Zpr.z_head in
        (hd, init, b, sw, tl)
      end
    | _ -> tc_error pf "code position does not lead to a while-loop"
  in

  let (init2, b2, sw2, tl) =
    if List.length tl < il then
      tc_error pf "1st first-loop is not followed by %d instruction(s)" il;
    let (init2, tl) = List.takedrop il tl in
      match tl with
      | { i_node = Swhile (b2, sw2) } :: tl -> (List.rev init2, b2, sw2, tl)
      | _ -> tc_error pf "cannot find the 2nd while-loop"
  in

  if d1 > List.length sw1.s_node then
    tc_error pf "in loop-fusion, body is less than %d instruction(s)" d1;
  if d2 > List.length sw2.s_node then
    tc_error pf "in loop-fusion, body is less than %d instruction(s)" d2;

  let (sw1, fini1) = List.takedrop d1 sw1.s_node in
  let (sw2, fini2) = List.takedrop d2 sw2.s_node in

  (* FIXME: costly *)
  if not (EcReduction.EqTest.for_stmt env (stmt init1) (stmt init2)) then
    tc_error pf "in loop-fusion, preludes do not match";
  if not (EcReduction.EqTest.for_stmt env (stmt fini1) (stmt fini2)) then
    tc_error pf "in loop-fusion, finalizers do not match";
  if not (EcReduction.EqTest.for_expr env b1 b2) then
    tc_error pf "in loop-fusion, while conditions do not match";

  check_independence (pf, hyps) b1 init1 sw1 sw2 fini1;

  let wl  = i_while (b1, stmt (sw1 @ sw2 @ fini1)) in
  let fus = List.rev_append init1 [wl] in

    (me, { zpr with Zpr.z_head = hd; Zpr.z_tail = fus @ tl; }, [])

let t_fusion_r side cpos infos g =
  let tr = fun side -> `LoopFusion (side, cpos, infos) in
  let cb = fun cenv _ me zpr -> fusion_stmt infos cenv me zpr in
  t_code_transform side
    ~bdhoare:true ~choare:None
    cpos tr (t_zip cb) g

let t_fusion = FApi.t_low3 "loop-fusion" t_fusion_r

(* -------------------------------------------------------------------- *)
let unroll_stmt (pf, _) me i =
  match i.i_node with
  | Swhile (e, sw) -> (me, [i_if (e, sw, stmt []); i])
  | _ -> tc_error pf "cannot find a while loop at given position"

let t_unroll_r side cpos g =
  let tr = fun side -> `LoopUnraoll (side, cpos) in
  t_code_transform side
    ~bdhoare:true ~choare:None
    cpos tr (t_fold unroll_stmt) g

let t_unroll = FApi.t_low2 "loop-unroll" t_unroll_r

(* -------------------------------------------------------------------- *)
let splitwhile_stmt b (pf, _) me i =
  match i.i_node with
  | Swhile (e, sw) ->
      let op_ty  = toarrow [tbool; tbool] tbool in
      let op_and = e_op EcCoreLib.CI_Bool.p_and [] op_ty in
      let e = e_app op_and [e; b] tbool in
        (me, [i_while (e, sw); i])

  | _ -> tc_error pf "cannot find a while loop at given position"

let t_splitwhile_r b side cpos g =
  let tr = fun side -> `SplitWhile (b, side, cpos) in
  t_code_transform side
    ~bdhoare:true ~choare:None
    cpos tr (t_fold (splitwhile_stmt b)) g

let t_splitwhile = FApi.t_low3 "split-while" t_splitwhile_r

(* -------------------------------------------------------------------- *)
let process_fission (side, cpos, infos) tc =
  t_fission side cpos infos tc

let process_fusion (side, cpos, infos) tc =
  t_fusion side cpos infos tc

let process_splitwhile (b, side, cpos) tc =
  let b =
    try  TTC.tc1_process_Xhl_exp tc side (Some tbool) b
    with EcFol.DestrError _ -> tc_error !!tc "goal must be a *HL statement"
  in t_splitwhile b side cpos tc

(* -------------------------------------------------------------------- *)
let process_unroll_for side cpos tc =
  if not (List.is_empty (fst cpos)) then
    tc_error !!tc "cannot use deep code position";

  let env  = FApi.tc1_env tc in
  let hyps = FApi.tc1_hyps tc in
  let c    = EcLowPhlGoal.tc1_get_stmt side tc in
  let z    = Zpr.zipper_of_cpos cpos c in
  let pos  = 1 + List.length z.Zpr.z_head in

  (* Extract loop condition / body *)
  let t, wbody  =
    match List.ohead z.Zpr.z_tail |> omap i_node with
    | Some (Swhile (t, wc)) -> t, wc
    | _ -> tc_error !!tc "the position must target a while loop" in

  (* Extract loop counter increment *)
  let x, z0 =
    match List.ohead z.Zpr.z_head |> omap i_node with
    | Some (Sasgn (LvVar (x, _), { e_node = Eint z0 })) -> x, z0
    | _ -> tc_error !!tc
             "the while loop must be preceded by an integer"
             "counter (constant) initialization" in

  (* Extract increment *)
  let eincr =
    match List.rev wbody.s_node with
    | { i_node = Sasgn (LvVar (x', _), e) } :: tl when pv_equal x x' ->
        if PV.mem_pv env x (is_write_r env PV.empty (List.rev tl)) then
          tc_error !!tc "the loop body must not modify the loop counter";
        e

    | _ -> tc_error !!tc
             "last instruction of the while loop must be"
             "an \"increment\" of the loop counter" in

  (* Apply loop increment *)
  let incrz =
    let fincr = form_of_expr mhr eincr in
    fun z0 ->
      let f = PVM.subst1 env x mhr (f_int z0) fincr in
      match (simplify full_red hyps f).f_node with
      | Fint z0 -> z0
      | _       -> tc_error !!tc "loop increment does not reduce to a constant" in

  (* Evaluate loop guard *)
  let test_cond =
    let ftest = form_of_expr mhr t in
    fun z0 ->
      let cond = PVM.subst1 env x mhr (f_int z0) ftest in
      match sform_of_form (simplify full_red hyps cond) with
      | SFtrue  -> true
      | SFfalse -> false
      | _       -> tc_error !!tc "while loop condition does not reduce to a constant" in

  let rec eval_cond z0 =
    if test_cond z0 then z0 :: eval_cond (incrz z0) else [z0] in

  let blen = List.length wbody.s_node in
  let zs   = eval_cond z0 in
  let hds  = Array.make (List.length zs) None in
  let m    = LDecl.fresh_id hyps "&m" in
  let x    = f_pvar x tint mhr in

  let t_set i pos z tc =
    hds.(i) <- Some (FApi.tc1_handle tc, pos, z); t_id tc in

  let t_conseq post tc =
    (EcPhlConseq.t_conseq (tc1_get_pre tc) post @+
    [ t_trivial; t_trivial; t_id]) tc in

  let rec t_doit i pos zs tc =
    match zs with
    | [] -> t_id tc
    | z :: zs ->
      ((t_rcond side (zs <> []) (Zpr.cpos pos) None) @+
      [FApi.t_try (t_intro_i m) @!
       t_conseq (f_eq x (f_int z)) @!
       t_set i pos z;
       t_doit (i+1) (pos + blen) zs]) tc in

  let t_conseq_nm tc =
    (EcPhlConseq.t_hoareS_conseq_nm (tc1_get_pre tc) f_true @+
    [ t_trivial; t_trivial; EcPhlTAuto.t_hoare_true]) tc in

  let doi i tc =
    if Array.length hds <= i then t_id tc else
    let (_h,pos,_z) = oget hds.(i) in
    if i = 0 then
      (EcPhlWp.t_wp (Some (Single (Zpr.cpos (pos - 2)))) @!
       t_conseq f_true @! EcPhlTAuto.t_hoare_true) tc
    else
      let (h', pos', z') = oget hds.(i-1) in
      FApi.t_seqs [
        EcPhlWp.t_wp (Some (Single (Zpr.cpos (pos-2))));
        EcPhlApp.t_hoare_app (Zpr.cpos (pos' - 1)) (f_eq x (f_int z')) @+
        [t_apply_hd h'; t_conseq_nm] ] tc
  in

  let tcenv = t_doit 0 pos zs tc in FApi.t_onalli doi tcenv

(* -------------------------------------------------------------------- *)
let process_unroll (side, cpos, for_) tc =
  if   for_
  then process_unroll_for side cpos tc
  else t_unroll side cpos tc
