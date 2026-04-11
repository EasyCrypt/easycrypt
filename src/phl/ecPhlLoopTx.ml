(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
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
type fission_t    = oside * pcodepos * (int * (int * int))
type fusion_t     = oside * pcodepos * (int * (int * int))
type unroll_t     = oside * pcodepos * [`While | `For of bool]
type splitwhile_t = pexpr * oside * pcodepos

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
let check_dslc pf =
  let error () =
    tc_error pf
      "epilog must be deterministic and loop/procedure-call free" in

  let rec doit_i c =
    match c.i_node with
    | Sasgn _ ->
       ()

    | Sif (_, c1, c2) ->
       List.iter doit_s [c1; c2]

    | Smatch (_, bs) ->
       List.iter (doit_s -| snd) bs

    | Srnd _ | Scall _ | Swhile _ | Sraise _  | Sabstract _ ->
       error ()

  and doit_s c =
    List.iter doit_i c.s_node

  in fun c -> List.iter doit_i c

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
  check_dslc pf s3;

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
    tc_error pf "in loop-fusion, epilogs do not match";
  if not (EcReduction.EqTest.for_expr env b1 b2) then
    tc_error pf "in loop-fusion, while conditions do not match";

  check_independence (pf, hyps) b1 init1 sw1 sw2 fini1;
  check_dslc pf fini1;

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
  t_code_transform side ~bdhoare:true cpos tr (t_fold unroll_stmt) g

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
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
  t_fission side cpos infos tc

let process_fusion (side, cpos, infos) tc =
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
  t_fusion side cpos infos tc

let process_splitwhile (b, side, cpos) tc =
  let b =
    try  TTC.tc1_process_Xhl_exp tc side (Some tbool) b
    with EcFol.DestrError _ -> tc_error !!tc "goal must be a *HL statement" in
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
  t_splitwhile b side cpos tc

(* -------------------------------------------------------------------- *)
let process_unroll_for ~cfold side cpos tc =
  let env  = FApi.tc1_env tc in
  let hyps = FApi.tc1_hyps tc in
  let (goal_m, _), c = EcLowPhlGoal.tc1_get_stmt side tc in

  if not (List.is_empty (fst cpos)) then
    tc_error !!tc "cannot use deep code position";

  let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
  let z, ((_nm_path, pos), _) = Zpr.zipper_of_cpos_r env cpos c in

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
    let fincr = ss_inv_of_expr goal_m eincr in
    fun z0 ->
      let f = map_ss_inv1 (PVM.subst1 env x goal_m (f_int z0)) fincr in
      match (simplify full_red hyps f.inv).f_node with
      | Fint z0 -> z0
      | _       -> tc_error !!tc "loop increment does not reduce to a constant" in

  (* Evaluate loop guard *)
  let test_cond =
    let ftest = ss_inv_of_expr goal_m t in
    fun z0 ->
      let cond = map_ss_inv1 (PVM.subst1 env x goal_m (f_int z0)) ftest in
      match sform_of_form (simplify full_red hyps cond.inv) with
      | SFtrue  -> true
      | SFfalse -> false
      | _       -> tc_error !!tc "while loop condition does not reduce to a constant" in

  let rec eval_cond z0 =
    if test_cond z0 then z0 :: eval_cond (incrz z0) else [z0] in

  let blen = List.length wbody.s_node in
  let zs   = eval_cond z0 in
  let hds  = Array.make (List.length zs) None in
  let m    = LDecl.fresh_id hyps "&m" in
  let x    = f_pvar x tint goal_m in

  (* Record the proof handle, position, and counter value for iteration [i].
     Used by [doi] below to revisit each unrolled iteration's subgoal. *)
  let t_set i pos z tc =
    hds.(i) <- Some (FApi.tc1_handle tc, pos, z); t_id tc in

  (* Strengthen the goal by replacing the current precondition with [post],
     closing the two side-conditions (pre ⇒ post, post ⇒ pre) via [t_trivial]. *)
  let t_conseq post tc =
    (EcPhlConseq.t_conseq (tc1_get_pre tc) post @+
    [ t_trivial; t_trivial; t_id]) tc in

  (* Main unrolling loop: processes the list [zs] of counter values produced
     by [eval_cond].  For each value [z]:
     1. Apply [t_rcond] at position [pos] (0-indexed) to split the while into
        its body (when [zs] is non-empty, i.e. guard is true) or skip it
        (when [zs] is empty, i.e. guard is false).
     2. On the "guard proved" subgoal: introduce the guard hypothesis,
        strengthen the pre to [x = z], and record iteration info via [t_set].
     3. On the "rest of program" subgoal: recurse with the next counter value,
        advancing [pos] by [blen] (the loop body length) since the unrolled
        body instructions now precede the remaining while.
     [pos] is a 0-indexed normalized position used to construct [cpos1 pos]. *)
  let rec t_doit i pos zs tc =
    match zs with
    | [] -> t_id tc
    | z :: zs ->
      ((t_rcond side (zs <> []) (EcMatching.Position.cpos1 pos)) @+
      [FApi.t_try (t_intro_i m) @!
       t_conseq (Inv_ss (map_ss_inv1 (fun x -> f_eq x (f_int z)) x)) @!
       t_set i pos z;
       t_doit (i+1) (pos + blen) zs]) tc in

  (* Close a subgoal of the form hoare[... : pre ==> true] by:
     1. Weakening the postcondition to hoare-with-no-memory via [t_hoareS_conseq_nm]
     2. Closing side conditions with [t_trivial]
     3. Closing the main goal with [t_hoare_true] *)
  let t_conseq_nm tc =
    match (tc1_get_pre tc) with
    | Inv_ss inv ->
      (EcPhlConseq.t_hoareS_conseq_nm
         inv
         { hsi_m = inv.m; hsi_inv = POE.empty f_true; }
       @+
       [ t_trivial; t_trivial; EcPhlTAuto.t_hoare_true]) tc
    | _ -> tc_error !!tc "expecting single sided precondition" in

  (* Second pass: revisit the subgoals recorded by [t_set] during [t_doit].
     For each iteration [i]:
     - [pos] is the 0-indexed position of the while loop (rcond target).
     - [init_pos] = pos - 1 is the counter init/increment assignment that
       precedes the while; WP must consume through it to evaluate [x = z].
     - i=0: WP from [init_pos] onward, strengthen pre to true, close with
       [t_hoare_true].
     - i>0: WP from [init_pos] onward, then seq-split at the previous
       iteration's rcond position [pos'] with postcondition [x = z'],
       applying the recorded proof handle [h'] and [t_conseq_nm]. *)
  let doi i tc =
    let open EcMatching.Position in
    if Array.length hds <= i then t_id tc else
    let (_h, pos, _z) = oget hds.(i) in
    let init_pos = pos - 1 in
    let wp_gap = GapBefore (cpos1 init_pos) in
    if i = 0 then
      (EcPhlWp.t_wp (Some (Single wp_gap)) @!
       t_conseq (Inv_ss {inv=f_true;m=x.m}) @! EcPhlTAuto.t_hoare_true) tc
    else
      let (h', pos', z') = oget hds.(i-1) in
      FApi.t_seqs [
        EcPhlWp.t_wp (Some (Single wp_gap));
        EcPhlSeq.t_hoare_seq (GapBefore (cpos1 pos')) (map_ss_inv2 f_eq x {m=goal_m;inv=f_int z'}) @+
        [t_apply_hd h'; t_conseq_nm] ] tc
  in

  let tcenv = t_doit 0 pos zs tc in
  let tcenv = FApi.t_onalli doi tcenv in

  if cfold then begin
    (* Use normalized position: pos - 1 is the loop counter initialization
       assignment that immediately precedes the while loop at pos.
       We cannot reuse the original match-based cpos here because t_doit
       has transformed the code, potentially invalidating the match. *)
    let cpos = ([], EcMatching.Position.cpos1 (pos - 1)) in
    let clen = blen * (List.length zs - 1) in

    FApi.t_last (EcPhlCodeTx.t_cfold ~eager:false side cpos (Some clen)) tcenv
  end else tcenv

(* -------------------------------------------------------------------- *)
let process_unroll (side, cpos, for_) tc =
  match for_ with
  | `While ->
    let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
    t_unroll side cpos tc

  | `For cfold ->
    process_unroll_for ~cfold side cpos tc
