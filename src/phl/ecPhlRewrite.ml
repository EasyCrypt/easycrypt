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
(* [proc rewrite] and [proc change] are derived, uniformly in every logic
   (hoare, ehoare, phoare, and equiv on one side): they resolve their
   arguments, check what they always checked (keeping their error
   messages), and apply a program transformation of the catalogue
   ([EcTrExprChange], [EcTrStmtChange]) through the transformation rule of
   the logic of the goal ([Ec<Logic>Transform]). The visible goals are
   those of that rule: the obligations of the transformation, then the
   transformed judgement.
   - [proc rewrite] (and [proc rewrite /=]): [EcTrExprChange], one
     equality [forall &m, forall locals, e = e'] per rewritten expression
     (in program order), each discharged on the spot by the tactic;
   - [proc change]: [EcTrStmtChange], one local equivalence between the
     replaced fragment and the new one (its frame computed by the rule
     from its precondition), left to the user.
   As they only differ by the transformation they apply, they share the
   logic-agnostic dispatcher [t_transform] below, and no per-logic module.
   [proc rewrite pre] is derived from [conseq]. *)

(* -------------------------------------------------------------------- *)
(* Apply the transformation [tr] through the transformation rule of the
   logic of the goal (on the given side for equiv). *)
let t_transform (side : side option) (tr : EcPlTransform.transform) (tc : tcenv1) =
  match side, (FApi.tc1_goal tc).f_node with
  | None, FhoareS _ ->
      EcHoareTransform.t_hoare_transform { htr_tr = tr } tc
  | None, FeHoareS _ ->
      EcEHoareTransform.t_ehoare_transform { ehtr_tr = tr } tc
  | None, FbdHoareS _ ->
      EcBdHoareTransform.t_bdhoare_transform { btr_tr = tr } tc
  | Some side, FequivS _ ->
      EcEquivTransform.t_equiv_transform { etr_side = side; etr_tr = tr } tc
  | _ ->
      EcLowPhlGoal.tc_error_noXhl
        ~kinds:(EcLowPhlGoal.hlkinds_Xhl_r `Stmt) !!tc

(* -------------------------------------------------------------------- *)
(* [t_change_range side range expr tc] applies [expr] to every expression
   of the instructions selected by [range] (the whole statement when
   [range] is [None]), recursing into the bodies of [if]/[while]/[match].
   [expr] receives the hypotheses extended with the match-arm locals in
   scope and returns [None] to leave an expression untouched.

   The expressions are enumerated as [EcTrExprChange] does; the
   replacements are applied by that transformation, which emits one
   equality side goal per rewritten expression, in program order,
   followed by the rewritten program-logic goal. Each side goal is of the
   form [forall &m, forall locals, e = e'] and is returned along with the
   identifiers to introduce to reach the equality. *)
let t_change_range
    (side  : side option)
    (range : EcMatching.Position.codegap_range option)
    (expr  : expr -> LDecl.hyps * memenv -> ('a * expr) option)
    (tc    : tcenv1)
=
  let hyps, concl = FApi.tc1_flat tc in
  let env = FApi.tc1_env tc in

  let kinds = [`Hoare `Stmt; `EHoare `Stmt; `PHoare `Stmt; `Equiv `Stmt] in

  if not (EcLowPhlGoal.is_program_logic concl kinds) then
    tc_error !!tc
      "conclusion should be a program logic \
      (hoare | ehoare | phoare | equiv)";

  let m, s = EcLowPhlGoal.tc1_get_stmt side tc in
  let mid = EcMemory.memory m in

  (* Match-arm locals are renamed apart from the hypotheses for the side
     goal; the transformation renames them back in the program. *)
  let change (locals : (EcIdent.t * ty) list) acc (e : expr) =
    let ids =
      LDecl.fresh_ids hyps (List.map (fun (x, _) -> EcIdent.name x) locals) in
    let fresh = List.map2 (fun id (_, ty) -> (id, ty)) ids locals in
    let hyps =
      List.fold_left
        (fun hyps (id, ty) -> LDecl.add_local id (LD_var (ty, None)) hyps)
        hyps fresh in

    let subst =
      List.fold_left2
        (fun subst (x, _) (y, ty) ->
          EcCoreSubst.bind_elocal subst x (EcTypes.e_local y ty))
        EcCoreSubst.Fsubst.f_subst_id locals fresh in

    match expr (EcCoreSubst.e_subst subst e) (hyps, m) with
    | None ->
        (None, None) :: acc, e

    | Some (data, e') ->
        (Some (ids, e'), Some (data, mid :: ids)) :: acc, e
  in

  let trange, acc =
    match range with
    | None ->
        None, fst (EcTrExprChange.exprs change [] s.s_node)

    | Some range ->
        let zpr, (_, body, _), nmr =
          try
            EcMatching.Zipper.zipper_and_split_of_cgap_range env range s
          with EcMatching.Position.InvalidCPos ->
            tc_error !!tc "invalid code position"
        in
        let locals = EcTrExprChange.locals_of_path zpr.z_path in
        Some nmr, fst (EcTrExprChange.exprs ~locals change [] body)
  in

  let changes, data = List.split (List.rev acc) in
  let data = List.pmap identity data in

  data,
  t_transform side
    (EcTrExprChange.TrExprChange
       { trec_range = trange; trec_exprs = changes; })
    tc

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
let tc1_process_range
  (tc   : tcenv1)
  (side : side option)
  (pos  : pcodepos_or_range option)
=
  Option.map
    (fun pos -> EcLowPhlGoal.tc1_process_codepos_or_range tc (side, pos))
    pos

(* -------------------------------------------------------------------- *)
let process_rewrite_rw
    (side : side option)
    (pos  : pcodepos_or_range option)
    (pt   : ppterm)
    (tc   : tcenv1)
=
  let hyps = FApi.tc1_hyps tc in

  (* Each expression gets its own instance of the proof term, so that the
     pattern variables can be instantiated independently. *)
  let patterns (hyps : LDecl.hyps) =
    let ptenv = EcProofTerm.ptenv_of_penv hyps !!tc in
    let pt = EcProofTerm.process_full_pterm ptenv pt in
    EcHiGoal.LowRewrite.find_rewrite_patterns `LtoR pt in

  let change (hyps : LDecl.hyps) (m : memenv) (e : expr) =
    let f = form_of_expr ~m:(fst m) e in
    try_rewrite_patterns hyps (patterns hyps) f
    |> Option.map (fun (data, f) ->
         data, expr_of_ss_inv { m = fst m; inv = f; }) in

  let discharge ((pt, mode, cpos), ids) (tc : tcenv1) =
    let cpos = EcMatching.FPosition.reroot [1] cpos in
    let tc = EcLowGoal.t_intros_i_1 ids tc in
    FApi.t_seq
      (EcLowGoal.t_rewrite ~mode pt (`LtoR, Some cpos))
      EcLowGoal.t_reflex
      tc
  in

  (* Fail early on an ill-formed proof term, even if no expression gets
     rewritten. *)
  ignore (patterns hyps : _ list);

  let range = tc1_process_range tc side pos in

  let change (e : expr) ((hyps, m) : LDecl.hyps * memenv) =
    change hyps m e in

  let data, tce = t_change_range side range change tc in

  if List.is_empty data then
    tc_error !!tc "cannot find a pattern to rewrite";

  FApi.t_sub (List.map discharge data @ [EcLowGoal.t_id]) tce

(* -------------------------------------------------------------------- *)
let process_rewrite_simpl
  (side : side option)
  (pos  : pcodepos_or_range option)
  (tc   : tcenv1)
=
  (* thread the proof-local simplify overlay (hint +db, local rules) so
     that [hint ...] and [with hint ... (proc rewrite /=)] are honored,
     as they are by [simplify]/[cbv] *)
  let ri =
    { EcReduction.nodelta with
        EcReduction.user_local = FApi.tc1_simplify_context tc } in

  let change (e : expr) ((hyps, me) : LDecl.hyps * memenv) =
    let f = ss_inv_of_expr (fst me) e in
    let f = map_ss_inv1 (EcCallbyValue.norm_cbv ri hyps) f in
    let e' = expr_of_ss_inv f in
    if e_equal e e' then None else Some (f, e')
  in

  let discharge (f, ids) =
    FApi.t_seqs [
      EcLowGoal.t_intros_i ids;
      EcLowGoal.t_change ~ri (map_ss_inv2 f_eq f f).inv;
      EcLowGoal.t_reflex
    ]
  in

  let range = tc1_process_range tc side pos in
  let data, tc = t_change_range side range change tc in
  FApi.t_sub (List.map discharge data @ [EcLowGoal.t_id]) tc

(* -------------------------------------------------------------------- *)
let process_rewrite
  (side : side option)
  (pos  : pcodepos_or_range option)
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
(* [t_change_stmt side pos binds s] replaces a code range with [s] (typed
   in the memory extended with the fresh locals [binds], as bound by
   [EcMemory.bindall_fresh]) through [EcTrStmtChange], generating:
   - a local equivalence goal showing that the original fragment and [s]
     agree under the framed precondition on the variables they both read,
     and produce the same values for everything observable afterwards;
   - the original program-logic goal with the selected range rewritten. *)
let t_change_stmt
   (side  : side option)
   (pos   : EcMatching.Position.codegap_range)
   (binds : ovariable list)
   (s     : stmt)
   (tc    : tcenv1)
=
  let env = FApi.tc1_env tc in

  let _, stmt = EcLowPhlGoal.tc1_get_stmt side tc in

  let _, _, nmr =
    try
      EcMatching.Zipper.zipper_and_split_of_cgap_range env pos stmt
    with EcMatching.Position.InvalidCPos ->
      tc_error !!tc "invalid code position"
  in

  t_transform side
    (EcTrStmtChange.TrStmtChange
       { trsc_range = nmr; trsc_binds = binds; trsc_stmt = s; })
    tc

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

  t_change_stmt side pos bindings s tc
