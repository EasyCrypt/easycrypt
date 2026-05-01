(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcParsetree

open EcCoreGoal
open EcCoreGoal.FApi
open EcHiGoal
open EcAst

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
type caseoption = {
  cod_ambient : bool;
}

module CaseOptions = struct
  let default = { cod_ambient = false; }

  let merged1 opts (b, x) =
    match x with
    | `Ambient -> { opts with cod_ambient  = b; }

  let merge1 opts ((b, x) : bool * EcParsetree.pcaseoption) =
    match x with
    | `Ambient -> { opts with cod_ambient = b; }

  let merge opts (specs : EcParsetree.pcaseoptions) =
    List.fold_left merge1 opts specs
end

(* -------------------------------------------------------------------- *)
let rec process1_by (ttenv : ttenv) (t : ptactic list option) (tc : tcenv1) =
  t_onall process_done (process1_seq ttenv (odfl [] t) tc)

(* -------------------------------------------------------------------- *)
and process1_solve (_ttenv : ttenv) (i, t) (tc : tcenv1) =
  let bases = omap (fun t -> List.map unloc t) t in
  process_solve ?bases ?depth:i tc

(* -------------------------------------------------------------------- *)
and process1_do (ttenv : ttenv) (b, n) (t : ptactic_core) (tc : tcenv1) =
  FApi.t_do b n (process1_core ttenv t) tc

(* -------------------------------------------------------------------- *)
and process1_or (ttenv : ttenv) (t1 : ptactic) (t2 : ptactic) (tc : tcenv1) =
  let t1 = process1 ttenv t1 in
  let t2 = process1 ttenv t2 in
  t_or t1 t2 tc

(* -------------------------------------------------------------------- *)
and process1_try (ttenv : ttenv) (t : ptactic_core) (tc : tcenv1) =
  FApi.t_try (process1_core ttenv t) tc

(* -------------------------------------------------------------------- *)
and process1_admit (_ : ttenv) (tc : tcenv1) =
  EcLowGoal.t_admit tc

(* -------------------------------------------------------------------- *)
and process1_idtac (_ : ttenv) (msg : string option) (tc : tcenv1) =
  msg |> oiter (EcEnv.notify (FApi.tc1_env tc) `Warning "%s");
  EcLowGoal.t_id tc

(* -------------------------------------------------------------------- *)
and process1_case (_ : ttenv) (doeq, opts, gp) (tc : tcenv1) =
  let opts = CaseOptions.merge CaseOptions.default opts in

  let form_of_gp () =
    match gp.pr_rev with
    | { pr_clear = []; pr_genp = [`Form (occ, pf)] }
        when List.is_empty gp.pr_view ->
     begin
       match occ with
       | None when not doeq -> pf
       | _ -> tc_error !!tc
          "cannot specify an occurence selector, nor eq. generation"
     end

    | _ -> tc_error !!tc "must give exactly one boolean formula"
  in
    match (FApi.tc1_goal tc).f_node with
    | FbdHoareS _ | FhoareS _ | FeHoareS _ when not opts.cod_ambient ->
        let _, fp = TTC.tc1_process_Xhl_formula tc (form_of_gp ()) in
        EcPhlCase.t_hl_case (Inv_ss fp) tc

    | FequivS _ when not opts.cod_ambient ->
        let fp = TTC.tc1_process_prhl_formula tc (form_of_gp ()) in
        EcPhlCase.t_equiv_case fp tc

    | _ -> EcHiGoal.process_case ~doeq gp tc

(* -------------------------------------------------------------------- *)
and process1_progress (ttenv : ttenv) options t (tc : tcenv1) =
  let t = t |> omap (process1_core ttenv) |> odfl EcLowGoal.t_id in

  let options =
    EcLowGoal.PGOptions.merge
      EcLowGoal.PGOptions.default
      options in

  FApi.t_seq
    EcHiGoal.process_trivial
    (EcLowGoal.t_progress ~options t)
    tc

(* -------------------------------------------------------------------- *)
and process1_seq (ttenv : ttenv) (ts : ptactic list) (tc : tcenv1) =
  let rec aux ts (tc : tcenv) : tcenv =
    match ts with
    | []      -> tc
    | t :: ts -> aux ts (process ttenv t tc)
  in

  aux ts (tcenv_of_tcenv1 tc)

(* -------------------------------------------------------------------- *)
and process1_nstrict (ttenv : ttenv) (t : ptactic_core) (tc : tcenv1) =
  if ttenv.tt_smtmode <> `Strict then
    tc_error !!tc "try! can only be used in strict proof mode";
  let ttenv = { ttenv with tt_smtmode = `Sloppy } in
  process1_try ttenv t tc

(* -------------------------------------------------------------------- *)
and process1_logic (ttenv : ttenv) (t : logtactic located) (tc : tcenv1) =
  let engine = process1_core ttenv in

  let tx =
    match unloc t with
    | Preflexivity        -> process_reflexivity
    | Passumption         -> process_assumption
    | Psmt pi             -> process_smt ~loc:(loc t) ttenv (Some pi)
    | Psplit i            -> process_split ?i
    | Pfield st           -> process_algebra `Solve `Field st
    | Pring st            -> process_algebra `Solve `Ring  st
    | Palg_norm           -> EcStrongRing.t_alg_eq
    | Pexists fs          -> process_exists fs
    | Pleft               -> process_left
    | Pright              -> process_right
    | Pcongr              -> process_congr
    | Ptrivial            -> process_trivial
    | Pelim pe            -> process_elim pe
    | Papply pe           -> process_apply ~implicits:ttenv.tt_implicits pe
    | Pcut (m, ip, f, t)  -> process_cut ~mode:m engine ttenv (ip, f, t)
    | Pcutdef (ip, f)     -> process_cutdef ttenv (ip, f)
    | Pmove pr            -> process_move pr.pr_view pr.pr_rev
    | Pclear l            -> process_clear l
    | Prewrite (ri, x)    -> process_rewrite ttenv ?target:x ri
    | Psubst   ri         -> process_subst ri
    | Psimplify ri        -> process_simplify ri
    | Pcbv ri             -> process_cbv ri
    | Pchange pf          -> process_change pf
    | Ppose (x, xs, o, p) -> process_pose x xs o p
    | Pmemory m           -> process_memory m
    | Pwlog (ids, b, f)   -> process_wlog ~suff:b ids f
    | Pgenhave gh         -> process_genhave ttenv gh
    | Prwnormal _         -> assert false
    | Pcoq (m, n, pi)     -> process_coq ~loc:(loc t) ~name:n.pl_desc ttenv m pi
  in
    tx tc

(* -------------------------------------------------------------------- *)
and process_conseqauto cm tc =
  let delta, tsolve = process_crushmode cm in
  EcPhlConseq.t_conseqauto ~delta ?tsolve tc

(* -------------------------------------------------------------------- *)
and process_dc_delay (side : oside) tc =
  match side with
  | None           -> EcPhlDCStruct.t_dc_delay tc
  | Some `Left     -> EcPhlDCStruct.t_dc_delay_side ~side:`Left tc
  | Some `Right    -> EcPhlDCStruct.t_dc_delay_side ~side:`Right tc

and process_dc_delay_star (side : side) (pre : pformula option) tc =
    match pre with
    | None -> EcPhlDCStruct.t_dc_delay_star ~side tc
    | Some pre ->
        let es = EcLowPhlGoal.tc1_as_dcEquivS tc in
        let m =
            match side with
            | `Left -> es.dces_ml
            | `Right -> es.dces_mr
        in
        let hyps = FApi.tc1_hyps tc in
        let hyps = EcEnv.LDecl.push_active_ss m hyps in
        let pre = TTC.pf_process_form !!tc hyps EcTypes.tbool pre in
        let pre = { m = fst m; inv = pre; } in
        EcPhlDCStruct.t_dc_delay_star ~side ~inv:pre tc

and process_dc_pop (side : oside) (n : int option) tc =
  let n = Option.value ~default:1 n in
  match side with
  | None        -> EcPhlDCStruct.t_dc_pop n tc
  | Some `Left  -> EcPhlDCStruct.t_dc_pop_side ~side:`Left n tc
  | Some `Right -> EcPhlDCStruct.t_dc_pop_side ~side:`Right n tc

and process_dc_push (side : oside) (n : int option) tc =
  let n = Option.value ~default:1 n in
  match side with
  | None        -> EcPhlDCStruct.t_dc_push n tc
  | Some `Left  -> EcPhlDCStruct.t_dc_push_side ~side:`Left n tc
  | Some `Right -> EcPhlDCStruct.t_dc_push_side ~side:`Right n tc

and process_dc_conseq pre post tc =
  let pre  = TTC.tc1_process_prhl_formula tc pre  in
  let post = TTC.tc1_process_prhl_formula tc post in
  EcPhlDCStruct.t_dc_conseq ~pre ~post tc

and process_dc_case theta tc =
  let theta = TTC.tc1_process_prhl_formula tc theta in
  EcPhlDCStruct.t_dc_case theta.inv tc

and process_dc_frame theta tc =
  let theta = TTC.tc1_process_prhl_formula tc theta in
  EcPhlDCStruct.t_dc_frame theta.inv tc

and process_dc_trans p12 q12 p23 q23 binds r2 c2 s2 tc =
    let hyps = FApi.tc1_hyps tc in
    let es = EcLowPhlGoal.tc1_as_dcEquivS tc in
    let m2 = EcMemory.empty_local ~witharg:false (EcIdent.create "&m") in

    (* Add the new variables *)
    let bindings =
        binds
        |> List.map (fun (xs, ty) -> List.map (fun x -> (x, ty)) xs)
        |> List.flatten
        |> List.map (fun (x, ty) ->
              let ty = EcProofTyping.process_type hyps ty in
              let x = Option.map EcLocation.unloc (EcLocation.unloc x) in
              EcAst.{ ov_name = x; ov_type = ty; }
              )
    in
    let m2, _ = EcMemory.bindall_fresh bindings m2 in

    let hyps = EcEnv.LDecl.push_active_ss m2 hyps in
    let r2 = EcProofTyping.process_stmt hyps r2 in
    let c2 = EcProofTyping.process_stmt hyps c2 in
    let s2 = EcProofTyping.process_stmt hyps s2 in

    let p12, q12 =
      let ml, mr = fst es.dces_ml, fst m2 in
      let hyps = EcEnv.LDecl.push_active_ts es.dces_ml m2 hyps in
      let p1 = TTC.pf_process_form !!tc hyps EcTypes.tbool p12 in
      let q1 = TTC.pf_process_form !!tc hyps EcTypes.tbool q12 in
      {ml;mr;inv=p1}, {ml;mr;inv=q1}
    in
    let p23, q23 =
      let ml, mr = fst m2, fst es.dces_mr in
      let hyps = EcEnv.LDecl.push_active_ts m2 es.dces_mr hyps in
      let p2 = TTC.pf_process_form !!tc hyps EcTypes.tbool p23 in
      let q2 = TTC.pf_process_form !!tc hyps EcTypes.tbool q23 in
      {ml;mr;inv=p2}, {ml;mr;inv=q2} 
    in

    EcPhlDCStruct.t_dc_trans p12 q12 p23 q23 m2 r2 c2 s2 tc


and process_dc_seq nl nr theta ts tc =
  let es = EcLowPhlGoal.tc1_as_dcEquivS tc in
  let theta = TTC.tc1_process_prhl_formula tc theta in
  let ts =
    match ts with
    | None -> None
    | Some (ptl, ptr) ->
        let open EcMaps in
        let ml = Mstr.add "r" es.dces_rl.s_node Mstr.empty in
        let ml = Mstr.add "s" es.dces_sl.s_node ml in
        let tl = TTC.tc1_process_prhl_stmt ~map:ml tc `Left  ptl in

        let mr = Mstr.add "r" es.dces_rr.s_node Mstr.empty in
        let mr = Mstr.add "s" es.dces_sr.s_node mr in
        let tr = TTC.tc1_process_prhl_stmt ~map:mr tc `Right ptr in
        Some (tl, tr)
  in
  EcPhlDCCore.t_dc_seq ~nl ~nr ?ts theta.inv tc

and process_dc_while side inv invr1 invr2 tc =
  let inv = TTC.tc1_process_prhl_formula tc inv in
  match side with
  | None ->
    let invr1 = omap (TTC.tc1_process_prhl_stmt tc `Left) invr1 in
    let invr2 = omap (TTC.tc1_process_prhl_stmt tc `Right) invr2 in
    EcPhlDCCore.t_dc_while ~inv ?invr1 ?invr2 tc
  | Some `Left ->
    let invr1 = omap (TTC.tc1_process_prhl_stmt tc `Left) invr1 in
    EcPhlDCCore.t_dc_while ~inv ?invr1 tc
  | Some `Right ->
    let invr2 = omap (TTC.tc1_process_prhl_stmt tc `Right) invr1 in
    EcPhlDCCore.t_dc_while ~inv ?invr2 tc

and process_fun_def_dispatch tc =
  match (EcCoreGoal.FApi.tc1_goal tc).f_node with
  | EcAst.FdcEquivF _ -> EcPhlDCCore.t_dc_fun_def tc
  | _ -> EcPhlFun.process_fun_def tc

and process_dc_unroll side tc =
  let side' = Option.value side ~default:`Left in
  EcPhlDCCore.t_dc_unroll_side ~side:side' tc

and process_dc_split side pe tc =
  let side' = Option.value side ~default:`Left in
  let e =
    TTC.tc1_process_Xhl_exp tc (Some side') (Some EcTypes.tbool) pe in
  EcPhlDCCore.t_dc_split_side ~side:side' e tc

and process_dc_rnd info tc =
  match info with
  | None -> EcPhlDCCore.t_dc_rnd None tc
  | Some (pf, pfinv) ->
      let f    = TTC.tc1_process_prhl_form_opt tc None pf    in
      let finv = TTC.tc1_process_prhl_form_opt tc None pfinv in
      let mk_builder ts : EcPhlDCCore.dc_bij_builder =
        fun _tyL _tyR -> ts
      in
      EcPhlDCCore.t_dc_rnd
        (Some (mk_builder f, mk_builder finv)) tc

(* -------------------------------------------------------------------- *)
and process1_phl (_ : ttenv) (t : phltactic located) (tc : tcenv1) =
  let (tx : tcenv1 -> tcenv) =
    match unloc t with
    | Pfun `Def                 -> process_fun_def_dispatch
    | Pfun (`Abs f)             -> EcPhlFun.process_fun_abs f
    | Pfun (`Upto info)         -> EcPhlFun.process_fun_upto info
    | Pfun `Code                -> EcPhlFun.process_fun_to_code
    | Pskip                     -> EcPhlSkip.t_skip
    | Pseq info                 -> EcPhlSeq.process_seq info
    | Pwp wp                    -> EcPhlWp.process_wp wp
    | Psp sp                    -> EcPhlSp.process_sp sp
    | Prcond (side, b, i)       -> EcPhlRCond.process_rcond side b i
    | Prmatch (side, c, i)      -> EcPhlRCond.process_rcond_match side c i
    | Pcond info                -> EcPhlHiCond.process_cond info
    | Pmatch infos              -> EcPhlHiCond.process_match infos
    | Pwhile (side, info)       -> EcPhlWhile.process_while side info
    | Pasyncwhile info          -> EcPhlWhile.process_async_while info
    | Pfission info             -> EcPhlLoopTx.process_fission info
    | Pfusion info              -> EcPhlLoopTx.process_fusion info
    | Punroll info              -> EcPhlLoopTx.process_unroll info
    | Psplitwhile info          -> EcPhlLoopTx.process_splitwhile info
    | Pcall (side, info)        -> EcPhlCall.process_call side info
    | Pcallconcave info         -> EcPhlCall.process_call_concave info
    | Pswap sw                  -> EcPhlSwap.process_swap sw
    | Pinline info              -> EcPhlInline.process_inline info
    | Poutline info             -> EcPhlOutline.process_outline info
    | Pinterleave info          -> EcPhlSwap.process_interleave info
    | Pcfold info               -> EcPhlCodeTx.process_cfold info
    | Pkill info                -> EcPhlCodeTx.process_kill info
    | PsimplifyIf info          -> EcPhlCodeTx.process_transform_if info
    | Pasgncase info            -> EcPhlCodeTx.process_case info
    | Palias info               -> EcPhlCodeTx.process_alias info
    | Pset info                 -> EcPhlCodeTx.process_set info
    | Psetmatch info            -> EcPhlCodeTx.process_set_match info
    | Pweakmem info             -> EcPhlCodeTx.process_weakmem info
    | Prnd (side, pos, info)    -> EcPhlRnd.process_rnd side pos info
    | Prndsem (red, side, pos)  -> EcPhlRnd.process_rndsem ~reduce:red side pos
    | Pconseq (opt, info)       -> EcPhlConseq.process_conseq_opt opt info
    | Pconseqauto cm            -> process_conseqauto cm
    | Pconcave info             -> EcPhlConseq.process_concave info
    | Phrex_elim                -> EcPhlExists.t_hr_exists_elim
    | Phrex_intro (fs, b)       -> EcPhlExists.process_exists_intro ~elim:b fs
    | Phecall (d, s, data)      -> EcPhlExists.process_ecall d s data
    | Pexfalso                  -> EcPhlAuto.t_exfalso
    | Pbydeno (mode, info)      -> EcPhlDeno.process_deno mode info
    | Pbyupto                   -> EcPhlUpto.process_uptobad
    | PPr pr                    -> EcPhlPr.process_ppr pr
    | Pfel (pos, info)          -> EcPhlFel.process_fel pos info
    | Phoare                    -> EcPhlBdHoare.t_hoare_bd_hoare
    | Pbdhoare_split i          -> EcPhlHiBdHoare.process_bdhoare_split i
    | Pprbounded                -> EcPhlPr.t_prbounded true
    | Psim (cm, info)           -> EcPhlEqobs.process_eqobs_in cm info
    | Ptrans_stmt info          -> EcPhlTrans.process_equiv_trans info
    | Prw_equiv info            -> EcPhlRwEquiv.process_rewrite_equiv info
    | Psymmetry                 -> EcPhlSym.t_equiv_sym
    | Peager_seq infos          -> curry3 EcPhlEager.process_seq infos
    | Peager_if                 -> EcPhlEager.process_if
    | Peager_while info         -> EcPhlEager.process_while info
    | Peager_fun_def            -> EcPhlEager.process_fun_def
    | Peager_fun_abs infos      -> EcPhlEager.process_fun_abs infos
    | Peager_call info          -> EcPhlEager.process_call info
    | Pdelay                    -> EcPhlDCDelay.t_delay
    | Pundelay                  -> EcPhlDCDelay.t_undelay
    | Pdc_delay side            -> process_dc_delay side
    | Pdc_delaystar (side, pre) -> process_dc_delay_star side pre
    | Pdc_pop (side, n)         -> process_dc_pop side n
    | Pdc_push (side, n)        -> process_dc_push side n
    | Pdc_conseq (pre, post)    -> process_dc_conseq pre post
    | Pdc_case theta            -> process_dc_case theta
    | Pdc_frame theta           -> process_dc_frame theta
    | Pdc_indep (nl, nr)        -> EcPhlDCStruct.t_dc_indep ~nl ~nr
    | Pdc_trans (p12, q12, p23, q23, bnds, r2, c2, s2) -> process_dc_trans p12 q12 p23 q23 bnds r2 c2 s2 
    | Pdc_skip                  -> EcPhlDCCore.t_dc_skip
    | Pdc_seq (nl, nr, theta, ts) -> process_dc_seq nl nr theta ts
    | Pdc_wp                    -> EcPhlDCCore.t_dc_wp None
    | Pdc_wp_side side          ->
        fun tc -> EcPhlDCCore.t_dc_wp_side ~side tc
    | Pdc_asgn_side side          ->
        fun tc -> EcPhlDCCore.t_dc_asgn_side side tc
    | Pdc_if None               -> EcPhlDCCore.t_dc_if
    | Pdc_if (Some side)        -> EcPhlDCCore.t_dc_if_side ~side
    | Pdc_while (side, inv, invr1, invr2) -> process_dc_while side inv invr1 invr2
    | Pdc_rnd (None, info)      -> process_dc_rnd info
    | Pdc_rnd (Some side, None) -> EcPhlDCCore.t_dc_rnd_side ~side
    | Pdc_rnd (Some _, Some _)  ->
        fun tc -> tc_error !!tc
          "one-sided dcoupl rnd does not take a bijection"
    | Pdc_sym                   -> EcPhlDCCore.t_dc_sym
    | Pdc_cond None             -> EcPhlDCCore.t_dc_cond_l
    | Pdc_cond (Some side)      -> EcPhlDCCore.t_dc_cond_side ~side
    | Pdc_cond_intro None       -> EcPhlDCCore.t_dc_cond_l_intro
    | Pdc_cond_intro (Some side) -> EcPhlDCCore.t_dc_cond_intro_side ~side
    | Pdc_prod side             ->
        let side' = Option.value side ~default:`Left in
        EcPhlDCCore.t_dc_prod_split ~side:side'
    | Pdc_prod_intro side       ->
        let side' = Option.value side ~default:`Left in
        EcPhlDCCore.t_dc_prod_intro ~side:side'
    | Pdc_unroll side           -> process_dc_unroll side
    | Pdc_split (side, e)       -> process_dc_split side e
    | Pbd_equiv (nm, f1, f2)    -> EcPhlConseq.process_bd_equiv nm (f1, f2)
    | Pauto                     -> EcPhlAuto.t_auto ~conv:`Conv
    | Plossless                 -> EcPhlHiAuto.t_lossless
    | Prepl_stmt infos          -> EcPhlTrans.process_equiv_trans infos
    | Pprocrewrite (s, p, f)    -> EcPhlRewrite.process_rewrite s p f
    | Pprocrewriteat (x, f)     -> EcPhlRewrite.process_rewrite_at x f
    | Pchangestmt (s, b, p, c)  -> EcPhlRewrite.process_change_stmt s b p c 
    | Prwprgm infos             -> EcPhlRwPrgm.process_rw_prgm infos
    | Phoaresplit               -> EcPhlHoare.process_hoaresplit
  in

  try  tx tc
  with (* PHL Specific low errors *)
  | EcLowPhlGoal.InvalidSplit is ->
      tc_error_lazy !!tc (fun fmt ->
        let ppe = EcPrinting.PPEnv.ofenv (FApi.tc1_env tc) in
        Format.fprintf fmt "invalid split index: %a"
        (fun fmt is -> match is with
        | `Gap gap -> Format.fprintf fmt "%a" EcPrinting.(pp_codegap1 ppe) gap
        | `Instr i -> Format.fprintf fmt "%a" EcPrinting.(pp_codepos1 ppe) i
        ) is)
          

(* -------------------------------------------------------------------- *)
and process_sub (ttenv : ttenv) tts tc =
  let count = FApi.tc_count tc in
  let ntacs = List.length tts in

  if count <> ntacs then
    tc_error !$tc "expecting %d tactic(s), got %d" count ntacs;
  FApi.t_sub (List.map (process1 ttenv) tts) tc

(* -------------------------------------------------------------------- *)
and process_fsub (ttenv : ttenv) (ts, t) tc =
  let ts = List.map (fst_map (process_tfocus tc)) ts in
  let tx i =
    ts
      |> List.ofind (fun (p, _) -> p i)
      |> (function Some (_, t) -> Some t | _ -> t)
      |> omap (process1 ttenv)
  in FApi.t_onfsub tx tc

(* -------------------------------------------------------------------- *)
and process_expect (ttenv : ttenv) ((t : pexpect), n) tc =
  if FApi.tc_count tc <> n then
    tc_error !$tc "expecting exactly %d subgoal(s), got %d" n (FApi.tc_count tc);

  match t with
  | `None     -> tc
  | `Tactic t -> FApi.t_onall (process1 ttenv t) tc
  | `Chain  t -> List.fold_left ((^~) (process_chain ttenv)) tc (unloc t)

(* -------------------------------------------------------------------- *)
and process_firsts (ttenv : ttenv) (t, i) tc =
  if i > FApi.tc_count tc then
    tc_error !$tc "expecting at least %d subgoal(s)" i;
  FApi.t_firsts (process1 ttenv t) i tc

(* -------------------------------------------------------------------- *)
and process_lasts (ttenv : ttenv) (t, i) tc =
  let count = FApi.tc_count tc in

  if i > count then
    tc_error !$tc "expecting at least %d subgoal(s)" i;
  FApi.t_lasts (process1 ttenv t) i tc

(* -------------------------------------------------------------------- *)
and process_rotate (_ttenv : ttenv) (d, i) tc =
  FApi.t_rotate d i tc

(* -------------------------------------------------------------------- *)
and process_focus (ttenv : ttenv) (t, p) tc =
  let p = EcHiGoal.process_tfocus tc p in
  FApi.t_onselect p (process1 ttenv t) tc

(* -------------------------------------------------------------------- *)
and process_chain (ttenv : ttenv) (t : ptactic_chain) (tc : tcenv) =
  match t with
  | Psubtacs  tactics -> process_sub    ttenv tactics tc
  | Pfsubtacs (ts, t) -> process_fsub   ttenv (ts, t) tc
  | Pfirst    (t, i)  -> process_firsts ttenv (t, i)  tc
  | Plast     (t, i)  -> process_lasts  ttenv (t, i)  tc
  | Protate   (d, i)  -> process_rotate ttenv (d, i)  tc
  | Pexpect   (t, n)  -> process_expect ttenv (t, n)  tc
  | Pfocus    (t, p)  -> process_focus  ttenv (t, p)  tc

(* -------------------------------------------------------------------- *)
and process_core (ttenv : ttenv) ({ pl_loc = loc } as t : ptactic_core) (tc : tcenv) =
  let tactic =
    match unloc t with
    | Pidtac    msg         -> `One (process1_idtac    ttenv msg)
    | Padmit                -> `One (process1_admit    ttenv)
    | Plogic    t           -> `One (process1_logic    ttenv (mk_loc loc t))
    | PPhl      t           -> `One (process1_phl      ttenv (mk_loc loc t))
    | Pby       t           -> `One (process1_by       ttenv t)
    | Psolve    t           -> `One (process1_solve    ttenv t)
    | Pdo       ((b, n), t) -> `One (process1_do       ttenv (b, n) t)
    | Ptry      t           -> `One (process1_try      ttenv t)
    | Por       (t1, t2)    -> `One (process1_or       ttenv t1 t2)
    | Pseq      ts          -> `One (process1_seq      ttenv ts)
    | Pcase     es          -> `One (process1_case     ttenv es)
    | Pprogress (o, t)      -> `One (process1_progress ttenv o t)
    | Psubgoal  tt          -> `All (process_chain     ttenv tt)
    | Pnstrict  t           -> `One (process1_nstrict  ttenv t)
  in
  (match tactic with `One t -> t_onall t | `All t -> t) tc

(* -------------------------------------------------------------------- *)
and process (ttenv : ttenv) (t : ptactic) (tc : tcenv) =
  let cf =
    match unloc t.pt_core with
    | Plogic (Pmove _)
    | Pidtac _ -> true
    | _ -> false
  in

  let tc = process_core ttenv t.pt_core tc in
  let tc = EcHiGoal.process_mgenintros ~cf ttenv t.pt_intros tc in
    tc

(* -------------------------------------------------------------------- *)
and process1_core (ttenv : ttenv) (t : ptactic_core) (tc : tcenv1) =
  process_core ttenv t (tcenv_of_tcenv1 tc)

(* -------------------------------------------------------------------- *)
and process1 (ttenv : ttenv) (t : ptactic) (tc : tcenv1) =
  process ttenv t (tcenv_of_tcenv1 tc)

(* -------------------------------------------------------------------- *)
let process (ttenv : ttenv) (t : ptactic list) (pf : proof) =
  if EcCoreGoal.closed pf then
    tc_error (proofenv_of_proof pf) "all goals are closed";

  let tc  = tcenv1_of_proof pf in
  let hd  = FApi.tc1_handle tc in
  let tc  = process1_seq ttenv t tc in
  let hds = FApi.tc_opened tc in
  ((hd, hds), proof_of_tcenv tc)
