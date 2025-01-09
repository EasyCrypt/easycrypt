(* -------------------------------------------------------------------- *)
open EcParsetree
open EcUtils
open EcAst
open EcCoreGoal
open EcEnv
open EcModules
open EcFol

(* -------------------------------------------------------------------- *)
let t_change
    (side : side option)
    (pos  : EcMatching.Position.codepos)
    (expr : expr -> LDecl.hyps * memenv -> 'a * expr)
    (tc   : tcenv1)
=
  let env, hyps, concl = FApi.tc1_eflat tc in

  let change (m : memenv) (i : instr) =
    let e, _, mk =
      EcUtils.ofdfl
        (fun () ->
           tc_error !!tc
             "targetted instruction should contain an expression")
        (get_expression_of_instruction i)
    in

    let data, e' = expr e (hyps, m) in
    let mid = EcMemory.memory m in

    let f  = form_of_expr mid e in
    let f' = form_of_expr mid e' in

    (data, [f_forall_mems [m] (f_eq f f')]), [mk e']
  in

  let kinds = [`Hoare `Stmt; `EHoare `Stmt; `PHoare `Stmt; `Equiv `Stmt] in

  if not (EcLowPhlGoal.is_program_logic concl kinds) then
    tc_error !!tc
      "conclusion should be a program logic \
      (hoare | ehoare | phoare | equiv)";

  let m, s = EcLowPhlGoal.tc1_get_stmt_with_memory side tc in
  let (data, goals), s =
    EcMatching.Zipper.map (FApi.tc1_env tc) pos (change m) s in
  let concl = EcLowPhlGoal.hl_set_stmt side concl s in

  data, FApi.xmutate1 tc `ProcChange (goals @ [concl])

(* -------------------------------------------------------------------- *)
let process_change
    (side : side option)
    (pos  : pcodepos)
    (form : pexpr)
    (tc   : tcenv1)
=
  let pos = EcProofTyping.tc1_process_codepos tc (side, pos) in

  let expr (e : expr) ((hyps, m) : LDecl.hyps * memenv) =
    let hyps = LDecl.push_active m hyps in
    let e =
      EcProofTyping.pf_process_exp
        !!tc hyps `InProc (Some e.e_ty) form
    in (), e
  in

  let (), tc = t_change side pos expr tc in tc

(* -------------------------------------------------------------------- *)
let process_rewrite_rw
    (side : side option)
    (pos  : pcodepos)
    (pt   : ppterm)
    (tc   : tcenv1)
=
  let hyps = FApi.tc1_hyps tc in
  let ptenv = EcProofTerm.ptenv_of_penv hyps !!tc in
  let pt = EcProofTerm.process_full_pterm ptenv pt in

  let pts = EcHiGoal.LowRewrite.find_rewrite_patterns `LtoR pt in

  let change (e : expr) ((hyps, m) : LDecl.hyps * memenv) =
    let e = form_of_expr (fst m) e in

    let try1 (pt, mode, (f1, f2)) =
      try
        let subf, occmode =
          EcProofTerm.pf_find_occurence_lazy
            pt.EcProofTerm.ptev_env ~ptn:f1 e
        in

        assert (EcProofTerm.can_concretize pt.ptev_env);

        let f2 = EcProofTerm.concretize_form pt.ptev_env f2 in
        let pt, _ = EcProofTerm.concretize pt in

        let cpos =
          EcMatching.FPosition.select_form
            ~xconv:`AlphaEq ~keyed:occmode.k_keyed
            hyps None subf e in

        let e = EcMatching.FPosition.map cpos (fun _ -> f2) e in

        Some ((pt, mode, cpos), e)

      with EcProofTerm.FindOccFailure _ ->
        None

    in

    let data, e =
      EcUtils.ofdfl
        (fun () -> tc_error !!tc "cannot find a pattern to rewrite")
        (List.find_map_opt try1 pts) in

    (m, data), expr_of_form (fst m) e
  in

  let pos = EcProofTyping.tc1_process_codepos tc (side, pos) in
  let (m, (pt, mode, cpos)), tc = t_change side pos change tc in
  let cpos = EcMatching.FPosition.reroot [1] cpos in

  let discharge (tc : tcenv1) =
    let tc = EcLowGoal.t_intros_i_1 [fst m] tc in
    FApi.t_seq
      (EcLowGoal.t_rewrite ~mode pt (`LtoR, Some cpos))
      EcLowGoal.t_reflex
      tc
  in

  FApi.t_first discharge tc

(* -------------------------------------------------------------------- *)
let process_rewrite_simpl
  (side : side option)
  (pos  : pcodepos)
  (tc   : tcenv1)
=
let ri = EcReduction.nodelta in

let change (e : expr) ((hyps, me) : LDecl.hyps * memenv) =
    let f = form_of_expr (fst me) e in
    let f = EcCallbyValue.norm_cbv ri hyps f in
    let e = expr_of_form (fst me) f in
    (fst me, f), e
  in

  let pos = EcProofTyping.tc1_process_codepos tc (side, pos) in
  let (m, f), tc = t_change side pos change tc in

  FApi.t_first (
    FApi.t_seqs [
      EcLowGoal.t_intro_s (`Ident m);
      EcLowGoal.t_change ~ri (f_eq f f);
      EcLowGoal.t_reflex
    ]
  ) tc

(* -------------------------------------------------------------------- *)
let process_rewrite
  (side : side option)
  (pos  : pcodepos)
  (rw   : prrewrite)
  (tc   : tcenv1)
=
  match rw with
  | `Rw rw -> process_rewrite_rw side pos rw tc
  | `Simpl -> process_rewrite_simpl side pos tc

(* -------------------------------------------------------------------- *)
let process_change_stmt 
  (side   : side option)
  ((p, o) : pcodepos1 * pcodeoffset1)
  (s      : pstmt)
  (tc     : tcenv1)
=
  let env = FApi.tc1_env tc in
  let me, stmt = EcLowPhlGoal.tc1_get_stmt_with_memory side tc in

  let p, o =
    let env = EcEnv.Memory.push_active me env in
    let pos = EcTyping.trans_codepos1 env p in
    let off = EcTyping.trans_codeoffset1 env o in
    let off = EcMatching.Position.resolve_offset ~base:pos ~offset:off in

    let start = EcMatching.Zipper.offset_of_position env pos stmt in
    let end_  = EcMatching.Zipper.offset_of_position env off stmt in

    if (end_ < start) then
      tc_error !!tc "end position cannot be before start position";

    (start - 1, end_ - start)
  in
    
  let stmt     = stmt.s_node in
  let hd, stmt = List.takedrop p stmt in
  let stmt, tl = List.takedrop o stmt in

  let s = EcProofTyping.tc1_process_stmt tc (snd me) s in

  let pvs = EcPV.is_write env (stmt @ s.s_node) in
  let pvs, globs = EcPV.PV.elements pvs in

  let eq =
    List.map
      (fun (pv, ty) -> f_eq (f_pvar pv ty mleft) (f_pvar pv ty mright))
      pvs
    @
    List.map
      (fun mp -> f_eqglob mp mleft mp mright)
      globs in

  let goal1 =
      f_equivS
        (mleft, snd me) (mright, snd me)
        f_true
        (EcAst.stmt stmt) s
        (f_ands eq)
  in

  let goal2 =
    EcLowPhlGoal.hl_set_stmt
      side (FApi.tc1_goal tc)
      (EcAst.stmt (List.flatten [hd; s.s_node; tl])) in

  FApi.xmutate1 tc `ProcChangeStmt [goal1; goal2]
