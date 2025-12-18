(* -------------------------------------------------------------------- *)
open EcParsetree
open EcUtils
open EcAst
open EcCoreGoal
open EcEnv
open EcModules
open EcFol
open Batteries
open EcLowPhlGoal

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

let rec pvtail (env: env) (pvs : EcPV.PV.t) (zp : Zpr.ipath) =
    let parent =
      match zp with
      | Zpr.ZTop -> None
      | Zpr.ZWhile (_, p) -> Some p
      | Zpr.ZIfThen (e, p, _) -> Some p
      | Zpr.ZIfElse (e, _, p) -> Some p
      | Zpr.ZMatch (e, p, _) -> Some p in
    match parent with
    | None -> pvs
    | Some ((_, tl), p) -> pvtail env (EcPV.PV.union pvs (EcPV.is_read env tl)) p

(* -------------------------------------------------------------------- *)
let t_change_stmt
  (side : side option)
  (pos : EcMatching.Position.codepos_range) 
  ((me, bindings) : memenv * ovariable list)
  (s : stmt)
  (tc : tcenv1)
=
  let env = FApi.tc1_env tc in
  let goal = (FApi.tc1_goal tc) in
  let post = match goal.f_node with
  | FhoareS { hs_po } -> hs_po
  | FbdHoareS { bhs_po } -> bhs_po
  | FeHoareS { ehs_po } -> ehs_po
  | FequivS { es_po } -> es_po
  | _ -> assert false
  in
  let _, stmt = EcLowPhlGoal.tc1_get_stmt side tc in 

  let env = EcEnv.Memory.push_active_ts me me env in (* FIXME *)

  let zpr, epos = Zpr.zipper_of_cpos_range env pos stmt in
  let stmt, epilog = match zpr.z_tail with
  | [] -> raise Zpr.InvalidCPos
  | i::tl -> let s, tl = Zpr.split_at_cpos1 env epos (EcAst.stmt tl) in
    (i::s), tl
  in

  let keep = pvtail env (EcPV.is_read env epilog) zpr.z_path in
  let keep = EcPV.PV.union keep (EcPV.PV.fv env (EcMemory.memory me) post) in

  let pvs = EcPV.is_write env (stmt @ s.s_node) in
  let _pvs, globs = EcPV.PV.elements pvs in

  let pvs, _ = EcPV.PV.elements (EcPV.PV.inter keep pvs) in

  let pre_pvs = EcPV.PV.inter 
    (EcPV.is_read env stmt) 
    (EcPV.is_read env s.s_node)
  in

  (* FIXME: Check | Do we need this? *)
(*
  let pre_pvs = EcPV.PV.union pre_pvs (
    pvtail env (EcPV.is_read env epilog) zpr.z_path
  ) in
*)

  (* Do we need this? *)
(*   let pre_pvs = EcPV.PV.union pre_pvs (EcPV.PV.fv env (EcMemory.memory me) post) in *)

  let pre_pvs, pre_globs = EcPV.PV.elements pre_pvs in

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

  let goal2 = match side, goal.f_node with
  | None, FhoareS hs -> f_hoareS (snd me) (hs_pr hs) stmt (hs_po hs)
  | None, FbdHoareS bhs -> f_bdHoareS (snd me) (bhs_pr bhs) stmt (bhs_po bhs) (bhs.bhs_cmp) (bhs_bd bhs)
  | None, FeHoareS ehs -> f_eHoareS (snd me) (ehs_pr ehs) stmt (ehs_po ehs)
  | Some `Left, FequivS es -> f_equivS (snd me) (snd es.es_mr) (es_pr es) stmt (es.es_sr) (es_po es)
  | Some `Right, FequivS es -> f_equivS (snd es.es_ml) (snd me) (es_pr es) (es.es_sl) stmt (es_po es)
  | _ -> assert false
  in

  FApi.xmutate1 tc `ProcChangeStmt [goal1; goal2]

(* -------------------------------------------------------------------- *)
let process_change_stmt
  (side   : side option)
  (binds  : ptybindings option)
  (pos    : pcodepos_range)
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
    EcTyping.trans_codepos_range ~memory:(fst me) env pos 
  in

(*
  let s = match side with 
  | Some side -> EcProofTyping.tc1_process_prhl_stmt tc side s
  | None -> EcProofTyping.tc1_process_Xhl_stmt tc s
  in
*)

  let bindings = 
     binds
  |> Option.default []
  |> List.map (fun (xs, ty) -> List.map (fun x -> (x, ty)) xs)
  |> List.flatten 
  |> List.map (fun (x, ty) ->
      let ue = EcUnify.UniEnv.create (Some (EcEnv.LDecl.tohyps hyps).h_tvar) in
      let ty = EcTyping.transty EcTyping.tp_tydecl env ue ty in
      assert (EcUnify.UniEnv.closed ue);
      let ty =
        let subst = EcCoreSubst.Tuni.subst (EcUnify.UniEnv.close ue) in
        EcCoreSubst.ty_subst subst ty in
      let x = Option.map EcLocation.unloc (EcLocation.unloc x) in
      let vr = EcAst.{ ov_name = x; ov_type = ty; } in
      vr
    )
  in
  let me, bindings = EcMemory.bindall_fresh bindings me in

  let env = EcEnv.Memory.push_active_ss me env in
  let s = 
    let ue = EcProofTyping.unienv_of_hyps hyps in
    let s = EcTyping.transstmt env ue s in

    assert (EcUnify.UniEnv.closed ue);

    let sb = EcCoreSubst.Tuni.subst (EcUnify.UniEnv.close ue) in
    EcCoreSubst.s_subst sb s 
  in

  t_change_stmt side pos (me, bindings) s tc
