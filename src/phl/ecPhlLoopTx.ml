(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcModules
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal

module Zpr = EcMatching.Zipper
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
type fission_t    = oside * codepos * (int * (int * int))
type fusion_t     = oside * codepos * (int * (int * int))
type unroll_t     = oside * codepos
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
    t_code_transform side ~bdhoare:true cpos tr (t_zip cb) g

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
    t_code_transform side ~bdhoare:true cpos tr (t_zip cb) g

let t_fusion = FApi.t_low3 "loop-fusion" t_fusion_r

(* -------------------------------------------------------------------- *)
let unroll_stmt (pf, _) me i =
  match i.i_node with
  | Swhile (e, sw) -> (me, [i_if (e, sw, stmt []); i])
  | _ -> tc_error pf "cannot find a while loop at given position"

let t_unroll_r side cpos g =
  let tr = fun side -> `LoopUnraoll (side, cpos) in
  t_code_transform side  ~bdhoare:true cpos tr (t_fold unroll_stmt) g

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
  t_code_transform side ~bdhoare:true cpos tr (t_fold (splitwhile_stmt b)) g

let t_splitwhile = FApi.t_low3 "split-while" t_splitwhile_r

(* -------------------------------------------------------------------- *)
let process_fission (side, cpos, infos) tc =
  t_fission side cpos infos tc

let process_fusion (side, cpos, infos) tc =
  t_fusion side cpos infos tc

let process_unroll (side, cpos) tc =
  t_unroll side cpos tc

let process_splitwhile (b, side, cpos) tc =
  let b =
    try  TTC.tc1_process_Xhl_exp tc side (Some tbool) b
    with EcFol.DestrError _ -> tc_error !!tc "goal must be a *HL statement"
  in t_splitwhile b side cpos tc
