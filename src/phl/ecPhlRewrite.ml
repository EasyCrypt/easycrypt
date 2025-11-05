(* -------------------------------------------------------------------- *)
open EcParsetree
open EcAst
open EcCoreGoal
open EcEnv
open EcModules
open EcFol
open Batteries

(* -------------------------------------------------------------------- *)
let t_change
    (side : side option)
    (pos  : EcMatching.Position.codepos)
    (expr : expr -> LDecl.hyps * memenv -> 'a * expr)
    (tc   : tcenv1)
=
  let hyps, concl = FApi.tc1_flat tc in

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

    let f  = ss_inv_of_expr mid e in
    let f' = ss_inv_of_expr mid e' in

    (data, [EcSubst.f_forall_mems_ss_inv m (map_ss_inv2 f_eq f f')]), [mk e']
  in

  let kinds = [`Hoare `Stmt; `EHoare `Stmt; `PHoare `Stmt; `Equiv `Stmt] in

  if not (EcLowPhlGoal.is_program_logic concl kinds) then
    tc_error !!tc
      "conclusion should be a program logic \
      (hoare | ehoare | phoare | equiv)";

  let m, s = EcLowPhlGoal.tc1_get_stmt side tc in
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
    let hyps = LDecl.push_active_ss m hyps in
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
    let e = ss_inv_of_expr (fst m) e in

    let try1 (pt, mode, (f1, f2)) =
      try
        let subf, occmode =
          EcProofTerm.pf_find_occurence_lazy
            pt.EcProofTerm.ptev_env ~ptn:f1 e.inv
        in
        let subf = { m=e.m; inv=subf } in

        assert (EcProofTerm.can_concretize pt.ptev_env);

        let f2 = EcProofTerm.concretize_form pt.ptev_env f2 in
        let pt, _ = EcProofTerm.concretize pt in

        let cpos = 
          EcMatching.FPosition.select_form
            ~xconv:`AlphaEq ~keyed:occmode.k_keyed
            hyps None subf.inv e.inv in

        let e = map_ss_inv1 (EcMatching.FPosition.map cpos (fun _ -> f2)) e in

        Some ((pt, mode, cpos), e)

      with EcProofTerm.FindOccFailure _ ->
        None

    in

    let data, e =
      EcUtils.ofdfl
        (fun () -> tc_error !!tc "cannot find a pattern to rewrite")
        (List.find_map_opt try1 pts) in

    (m, data), expr_of_ss_inv e
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
    let f = ss_inv_of_expr (fst me) e in
    let f = map_ss_inv1 (EcCallbyValue.norm_cbv ri hyps) f in
    let e = expr_of_ss_inv f in
    (fst me, f), e
  in

  let pos = EcProofTyping.tc1_process_codepos tc (side, pos) in
  let (m, f), tc = t_change side pos change tc in

  FApi.t_first (
    FApi.t_seqs [
      EcLowGoal.t_intro_s (`Ident m);
      EcLowGoal.t_change ~ri (map_ss_inv2 f_eq f f).inv;
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
let t_change_stmt
  (side : side option)
  (pos : EcMatching.Position.codepos_range) 
  (s : stmt)
  (tc : tcenv1)
=
  let env = FApi.tc1_env tc in
  let me, stmt = EcLowPhlGoal.tc1_get_stmt side tc in 

  let (zpr, _), (stmt, epilog) = EcMatching.Zipper.zipper_and_split_of_cpos_range env pos stmt in

  let pvs = EcPV.is_write env (stmt @ s.s_node) in
  let pvs, globs = EcPV.PV.elements pvs in

  let pre_pvs, pre_globs = EcPV.PV.elements @@ EcPV.PV.inter 
    (EcPV.is_read env stmt) 
    (EcPV.is_read env s.s_node)
  in

  let mleft = EcIdent.create "&1" in (* FIXME: PR: is this how we want to do this? *)
  let mright = EcIdent.create "&2" in

  let eq =
   List.map
     (fun (pv, ty) -> f_eq (f_pvar pv ty mleft).inv (f_pvar pv ty mright).inv)
     pvs
   @
   List.map
     (fun mp -> f_eqglob mp mleft mp mright)
     globs in

  let pre_eq = 
    List.map
      (fun (pv, ty) -> f_eq (f_pvar pv ty mleft).inv (f_pvar pv ty mright).inv)
      pre_pvs
    @
    List.map
      (fun mp -> f_eqglob mp mleft mp mright)
      pre_globs
    in

  let goal1 =
     f_equivS
       (snd me) (snd me)
       {ml=mleft; mr=mright; inv=f_ands pre_eq} 
       (EcAst.stmt stmt) s
       {ml=mleft; mr=mright; inv=f_ands eq}
  in

  let stmt = EcMatching.Zipper.zip { zpr with z_tail = s.s_node @ epilog } in

  let goal2 =
   EcLowPhlGoal.hl_set_stmt
     side (FApi.tc1_goal tc)
     stmt in

  FApi.xmutate1 tc `ProcChangeStmt [goal1; goal2]

(* -------------------------------------------------------------------- *)
let process_change_stmt
  (side   : side option)
  (pos    : pcodepos_range)
  (s      : pstmt)
  (tc     : tcenv1)
=
  let env = FApi.tc1_env tc in

  begin match side, (FApi.tc1_goal tc).f_node with
  | _, FhoareF _ 
  | _, FeHoareF _
  | _, FequivF _
  | _, FbdHoareF _ -> tc_error !!tc "Expecting goal with inlined program code"
  | Some _, FhoareS _ 
  | Some _, FeHoareS _
  | Some _, FbdHoareS _-> tc_error !!tc "Tactic should not receive side for non-relational goal"
  | None, FequivS _ -> tc_error !!tc "Tactic requires side selector for relational goal"
  | None, FhoareS _ 
  | None, FeHoareS _
  | None, FbdHoareS _
  | Some _ , FequivS _ -> ()
  | _ -> tc_error !!tc "Wrong goal shape, expecting hoare or equiv goal with inlined code"
  end;

  let me, _ = EcLowPhlGoal.tc1_get_stmt side tc in 

  let pos = 
    let env = EcEnv.Memory.push_active_ss me env in
    EcTyping.trans_codepos_range ~memory:(fst me) env pos 
  in

  let s = match side with 
  | Some side -> EcProofTyping.tc1_process_prhl_stmt tc side s
  | None -> EcProofTyping.tc1_process_Xhl_stmt tc s 
  in

  t_change_stmt side pos s tc
