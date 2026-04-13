(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcCoreGoal
open EcEnv
open EcModules
open EcFol

module L  = EcLocation
module PT = EcProofTerm

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
  let pos = EcLowPhlGoal.tc1_process_codepos tc (side, pos) in

  let expr (e : expr) ((hyps, m) : LDecl.hyps * memenv) =
    let hyps = LDecl.push_active_ss m hyps in
    let e =
      EcProofTyping.pf_process_exp
        !!tc hyps `InProc (Some e.e_ty) form
    in (), e
  in

  let (), tc = t_change side pos expr tc in tc

(* -------------------------------------------------------------------- *)
let try_rewrite_patterns
  (hyps   : LDecl.hyps)
  (pts    : (PT.pt_ev * EcLowGoal.rwmode * (form * form)) list)
  (target : form)
=
  let try1 (pt, mode, (f1, f2)) =
    try
      let subf, occmode =
        EcProofTerm.pf_find_occurence_lazy
          pt.EcProofTerm.ptev_env ~ptn:f1 target
      in

      assert (EcProofTerm.can_concretize pt.ptev_env);

      let f2 = EcProofTerm.concretize_form pt.ptev_env f2 in
      let pt, _ = EcProofTerm.concretize pt in

      let cpos =
        EcMatching.FPosition.select_form
          ~xconv:`AlphaEq ~keyed:occmode.k_keyed
          hyps None subf target in

      let target = EcMatching.FPosition.map cpos (fun _ -> f2) target in

      Some ((pt, mode, cpos), target)

    with EcProofTerm.FindOccFailure _ ->
      None

  in List.find_map_opt try1 pts

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
    let e = form_of_expr ~m:(fst m) e in

    let data, e =
      EcUtils.ofdfl
        (fun () -> tc_error !!tc "cannot find a pattern to rewrite")
        (try_rewrite_patterns hyps pts e) in

    (m, data), (expr_of_ss_inv { m = fst m; inv = e; })
  in

  let pos = EcLowPhlGoal.tc1_process_codepos tc (side, pos) in
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

  let pos = EcLowPhlGoal.tc1_process_codepos tc (side, pos) in
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
let process_rewrite_at
  (where : psymbol)
  (pt    : ppterm)
  (tc    : tcenv1)
=
  if L.unloc where <> "pre" then begin
    tc_error !!tc "can only rewrite in pre-condition"
  end;

  let pre  = EcLowPhlGoal.tc1_get_pre tc in
  let post = EcLowPhlGoal.tc1_get_post tc in

  let tophyps = FApi.tc1_hyps tc in

  let mems, hyps = EcLowPhlGoal.push_memenvs_pre tophyps (FApi.tc1_goal tc) in
  let pre = EcSubst.inv_rebind pre (List.fst mems) in

  let ptenv = EcProofTerm.ptenv_of_penv hyps !!tc in
  let pt = EcProofTerm.process_full_pterm ptenv pt in
  let pts = EcHiGoal.LowRewrite.find_rewrite_patterns `LtoR pt in

  let (pt, mode, cpos), pre =
    let data, cpre =
      EcUtils.ofdfl
        (fun () -> tc_error !!tc "cannot find a pattern to rewrite")
        (try_rewrite_patterns hyps pts (inv_of_inv pre)) in
    (data, map_inv1 (fun _ -> cpre) pre) in

  let t_pre (tc : tcenv1) =
    let ids = List.fst mems in
    let h1 = EcIdent.create "_" in
    let h2 = EcIdent.create "_" in

    let+ tc = EcLowGoal.t_intros_i ids tc in
    let+ tc = EcLowGoal.t_duplicate_top_assumtion tc in
    let+ tc = EcLowGoal.t_intros_i [h1; h2] tc in

       EcLowGoal.t_rewrite ~mode ~target:h2 pt (`LtoR, Some cpos) tc
    |> FApi.t_last (EcLowGoal.t_apply_hyp h2)
    |> FApi.t_onall (EcLowGoal.t_generalize_hyp ~clear:`Yes h1)
    |> FApi.t_onall (EcLowGoal.t_generalize_hyps ~clear:`Yes ids) in

  let t_post (tc : tcenv1) =
    let ids = List.map (fun _ -> EcIdent.create "_") mems in
    let h = EcIdent.create "_" in
    let+ tc = EcLowGoal.t_intros_i (ids @ [h]) tc in
    EcLowGoal.t_apply_hyp h tc in

  EcPhlConseq.t_conseq pre post tc
  |> FApi.t_sub [t_pre; t_post; EcLowGoal.t_id]

(* -------------------------------------------------------------------- *)
(* [t_change_stmt side pos ?me s] replaces a code range with [s] by
   generating:
   - a local equivalence goal showing that the original fragment and [s]
     agree under the framed precondition on the variables they both read,
     and produce the same values for everything observable afterwards;
   - the original program-logic goal with the selected range rewritten.

   If [me] is provided, it is used as the memory environment (e.g. when
   fresh local variables have been bound); otherwise, the memory
   environment is taken from the goal. *)
let t_change_stmt
   (side : side option)
   (pos  : EcMatching.Position.codegap_range)
  ?(me   : memenv option)
   (s    : stmt)
   (tc   : tcenv1)
=
  let env = FApi.tc1_env tc in

  let me, stmt =
    let metc, stmt = EcLowPhlGoal.tc1_get_stmt side tc in
    (odfl metc me, stmt)
  in

  let zpr, (_,stmt, epilog), _nmr =
    EcMatching.Zipper.zipper_and_split_of_cgap_range env pos stmt in

  (* Collect the variables that may be modified by the surrounding context,
     excluding the fragment being replaced. *)
  let modi =
    let zpr = { zpr with z_tail = epilog } in
    let zpr = (zpr.z_head, zpr.z_tail), zpr.z_path in
    EcPV.zpr_pv `Write `Before env EcPV.PV.empty zpr in

  (* Keep only the top-level conjuncts of the current precondition that talk
     about the active memory and are independent from the surrounding writes. *)
  let frame =
    let filter (f : form) =
      let pvs = EcPV.form_read env EcPV.PMVS.empty f in
      let pvs_me = EcIdent.Mid.find_def EcPV.PV.empty (fst me) pvs in
      let pvs = EcIdent.Mid.remove (fst me) pvs in

         EcIdent.Mid.is_empty pvs
      && (EcPV.PV.indep env modi pvs_me) in

    EcFol.filter_topand_form
      filter
      (inv_of_inv (EcLowPhlGoal.tc1_get_pre tc)) in

  let written = EcPV.PV.empty in
  let written = EcPV.is_write_r env written stmt in
  let written = EcPV.is_write_r env written s.s_node in

  let obs =
    let zpr = { zpr with z_tail = epilog } in
    let zpr = (zpr.z_head, zpr.z_tail), zpr.z_path in
    let obs = EcPV.zpr_pv `Read `After env EcPV.PV.empty zpr in

    let goal =
      let pvs =
        EcLowPhlGoal.logicS_post_read env
          (EcLowPhlGoal.get_logicS (FApi.tc1_goal tc))
      in
      EcIdent.Mid.find_def EcPV.PV.empty (fst me) pvs
    in

    EcPV.PV.union obs goal
  in

  let written = EcPV.PV.inter written obs in

  (* The local equivalence goal relates shared reads in the precondition and
     the writes that remain observable in the continuation/postcondition. *)
  let wr_pvs, wr_globs = EcPV.PV.elements written in

  let pr_pvs, pr_globs = EcPV.PV.elements @@ EcPV.PV.inter
    (EcPV.is_read env stmt)
    (EcPV.is_read env s.s_node)
  in

  let ml = EcIdent.create "&1" in
  let mr = EcIdent.create "&2" in

  let frame = omap (fun frame ->
    let subst = EcSubst.add_memory EcSubst.empty (fst me) ml in
    EcSubst.subst_form subst frame) frame in

  let mk_pv_eq ((pv, ty) : prog_var * ty) =
    f_eq (f_pvar pv ty ml).inv (f_pvar pv ty mr).inv

  and mk_glob_eq (mp : EcPath.mpath) =
    f_eqglob mp ml mp mr

  in

  let pr_eq = List.map mk_pv_eq pr_pvs @ List.map mk_glob_eq pr_globs in
  let po_eq = List.map mk_pv_eq wr_pvs @ List.map mk_glob_eq wr_globs in

  (* First subgoal: prove that the replacement fragment preserves the
     observable behavior required by the outer proof. *)
  let goal1 =
    f_equivS
      (snd me) (snd me)
      { ml; mr; inv = ofold f_and (f_ands pr_eq) frame; }
      (EcAst.stmt stmt) s
      { ml; mr; inv = f_ands po_eq; }
  in

  let stmt = EcMatching.Zipper.zip { zpr with z_tail = s.s_node @ epilog } in

  (* Second subgoal: continue with the original goal after rewriting the
     selected statement range. *)
  let goal2 =
   EcLowPhlGoal.hl_set_stmt
     side (FApi.tc1_goal tc)
     stmt in

  FApi.xmutate1 tc `ProcChangeStmt [goal1; goal2]

(* -------------------------------------------------------------------- *)
let process_change_stmt
  (side   : side option)
  (binds  : ptybindings option)
  (pos    : prange1_or_insert)
  (s      : pstmt)
  (tc     : tcenv1)
=
  let hyps = FApi.tc1_hyps tc in
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
    EcTyping.trans_range1_or_insert ~memory:(fst me) env pos
  in

  (* Add the new variables *)
  let bindings =
     binds
  |> odfl []
  |> List.map (fun (xs, ty) -> List.map (fun x -> (x, ty)) xs)
  |> List.flatten
  |> List.map (fun (x, ty) ->
      let ty = EcProofTyping.process_type hyps ty in
      let x = Option.map EcLocation.unloc (EcLocation.unloc x) in
      EcAst.{ ov_name = x; ov_type = ty; }
    )
  in
  let me, _ = EcMemory.bindall_fresh bindings me in

  (* Process the given statement using the new bound variables *)
  let hyps = EcEnv.LDecl.push_active_ss me hyps in
  let s = EcProofTyping.process_stmt hyps s in

  t_change_stmt side pos ~me s tc
