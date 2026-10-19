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

module Pos = EcMatching.Position
module Zpr = EcMatching.Zipper
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
type fission_t    = oside * pcodepos * (int * (int * int))
type fusion_t     = oside * pcodepos * (int * (int * int))
type unroll_t     = oside * pcodepos * [`While | `For of bool]
type splitwhile_t = pexpr * oside * pcodepos

(* -------------------------------------------------------------------- *)
(* Derived tactics. The loop transformations are entries of the
   transformation catalogue, applied through the transformation rule of
   the goal's logic ([t_<logic>_transform]; equiv: on the given side):

     t_fission side p (n, (d1, d2))   [EcTrFission.TrFission]
     t_fusion  side p (n, (d1, d2))   [EcTrFusion.TrFusion]
     t_unroll  side p                 [EcTrUnroll.TrUnroll]
     t_splitwhile b side p            [EcTrSplitWhile.TrSplitWhile]

   Each one resolves the code position [p] in the transformed statement
   (failing with "invalid code position"), then applies the rule, which
   runs the entry and reports its failures. No obligation: the only
   visible goal is the transformed judgement, same pre / postconditions.
   They are uniform across logics, hence a single dispatcher here rather
   than one module per logic that would only hold a one-line call. The
   [process_*] entries type the position (and the condition of
   [splitwhile]) in the memory of the transformed statement.

   [unroll for] ([process_unroll_for]) stays derived: rcond, wp, seq,
   conseq and cfold. *)

(* -------------------------------------------------------------------- *)
(* Resolve [cpos] in [s] to a normalized (possibly nested) position. *)
let resolve_cpos (tc : tcenv1) (cpos : Pos.codepos) (s : stmt) =
  try  fst (snd (Zpr.zipper_of_cpos_r (FApi.tc1_env tc) cpos s))
  with Pos.InvalidCPos -> tc_error !!tc "invalid code position"

(* Apply the transformation [tr at], [at] being [cpos] resolved in the
   transformed statement, through the transformation rule of the goal's
   logic (equiv: of [side]). *)
let t_loop_transform
    side cpos (tr : Pos.nm_codepos -> EcPlTransform.transform) tc
=
  match side, (FApi.tc1_goal tc).f_node with
  | None, FhoareS hs ->
      EcHoareTransform.t_hoare_transform
        { htr_tr = tr (resolve_cpos tc cpos hs.hs_s) } tc

  | None, FeHoareS hs ->
      EcEHoareTransform.t_ehoare_transform
        { ehtr_tr = tr (resolve_cpos tc cpos hs.ehs_s) } tc

  | None, FbdHoareS hs ->
      EcBdHoareTransform.t_bdhoare_transform
        { btr_tr = tr (resolve_cpos tc cpos hs.bhs_s) } tc

  | None, _ ->
      tc_error_noXhl ~kinds:[`PHoare `Stmt; `Hoare `Stmt; `EHoare `Stmt] !!tc

  | Some side, _ ->
      let es = tc1_as_equivS tc in
      let s  = sideif side es.es_sl es.es_sr in
      EcEquivTransform.t_equiv_transform
        { etr_side = side; etr_tr = tr (resolve_cpos tc cpos s) } tc

(* -------------------------------------------------------------------- *)
let t_fission side cpos (il, (d1, d2)) =
  t_loop_transform side cpos (fun at ->
    EcTrFission.TrFission
      { trfi_at = at; trfi_init = il; trfi_d1 = d1; trfi_d2 = d2; })

let t_fusion side cpos (il, (d1, d2)) =
  t_loop_transform side cpos (fun at ->
    EcTrFusion.TrFusion
      { trfu_at = at; trfu_init = il; trfu_d1 = d1; trfu_d2 = d2; })

let t_unroll side cpos =
  t_loop_transform side cpos (fun at ->
    EcTrUnroll.TrUnroll { trun_at = at; })

let t_splitwhile b side cpos =
  t_loop_transform side cpos (fun at ->
    EcTrSplitWhile.TrSplitWhile { trsw_at = at; trsw_cond = b; })

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
             "last instruction of the while loop must be \
              an \"increment\" of the loop counter" in

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
