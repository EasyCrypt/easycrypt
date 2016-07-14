(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcParsetree
open EcFol

open EcCoreGoal
open EcCoreGoal.FApi
open EcHiGoal

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
let rec process1_debug (_ttenv : ttenv) (tc : tcenv1) =
  FApi.tcenv_of_tcenv1 tc

(* -------------------------------------------------------------------- *)
and process1_by (ttenv : ttenv) (t : ptactic list option) (tc : tcenv1) =
  t_onall process_done (process1_seq ttenv (odfl [] t) tc)

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
  EcFortune.pick () |> oiter (EcEnv.notify (FApi.tc1_env tc) `Warning "%s");
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
    | FbdHoareS _ | FhoareS _ when not opts.cod_ambient ->
        let fp = TTC.tc1_process_Xhl_formula tc (form_of_gp ()) in
        EcPhlCase.t_hl_case fp tc

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
and process1_logic (ttenv : ttenv) (t : logtactic located) (tc : tcenv1) =
  let engine = process1_core ttenv in

  let tx =
    match unloc t with
    | Preflexivity      -> process_reflexivity
    | Passumption       -> process_assumption
    | Psmt pi           -> process_smt ~loc:(loc t) ttenv pi
    | Psplit            -> process_split
    | Pfield st         -> process_algebra `Solve `Field st
    | Pring st          -> process_algebra `Solve `Ring  st
    | Palg_norm         -> EcStrongRing.t_alg_eq
    | Pexists fs        -> process_exists fs
    | Pleft             -> process_left
    | Pright            -> process_right
    | Pcongr            -> process_congr
    | Ptrivial          -> process_trivial
    | Pelim pe          -> process_elim pe
    | Papply pe         -> process_apply ~implicits:ttenv.tt_implicits pe
    | Pcut (m, ip, f, t)-> process_cut ~mode:m engine ttenv (ip, f, t)
    | Pcutdef (ip, f)   -> process_cutdef ttenv (ip, f)
    | Pmove pr          -> process_move pr.pr_view pr.pr_rev
    | Pclear l          -> process_clear l
    | Prewrite (ri, x)  -> process_rewrite ttenv ?target:x ri
    | Psubst   ri       -> process_subst ri
    | Psimplify ri      -> process_simplify ri
    | Pchange pf        -> process_change pf
    | Ppose (x, o, p)   -> process_pose x o p

    | _ -> assert false
  in
    tx tc

(* -------------------------------------------------------------------- *)
and process1_phl (_ : ttenv) (t : phltactic located) (tc : tcenv1) =
  let (tx : tcenv1 -> tcenv) =
    match unloc t with
    | Pfun `Def                 -> EcPhlFun.process_fun_def
    | Pfun (`Abs f)             -> EcPhlFun.process_fun_abs f
    | Pfun (`Upto info)         -> EcPhlFun.process_fun_upto info
    | Pfun `Code                -> EcPhlFun.process_fun_to_code
    | Pskip                     -> EcPhlSkip.t_skip
    | Papp info                 -> EcPhlApp.process_app info
    | Pwp wp                    -> EcPhlWp.t_wp wp
    | Psp sp                    -> EcPhlSp.t_sp sp
    | Prcond (side, b, i)       -> EcPhlRCond.t_rcond side b i
    | Pcond side                -> EcPhlCond.process_cond side
    | Pwhile (side, info)       -> EcPhlWhile.process_while side info
    | Pasyncwhile info          -> EcPhlWhile.process_async_while info
    | Pfission info             -> EcPhlLoopTx.process_fission info
    | Pfusion info              -> EcPhlLoopTx.process_fusion info
    | Punroll info              -> EcPhlLoopTx.process_unroll info
    | Psplitwhile info          -> EcPhlLoopTx.process_splitwhile info
    | Pcall (side, info)        -> EcPhlCall.process_call side info
    | Pswap sw                  -> EcPhlSwap.process_swap sw
    | Pinline info              -> EcPhlInline.process_inline info
    | Pcfold info               -> EcPhlCodeTx.process_cfold info
    | Pkill info                -> EcPhlCodeTx.process_kill info
    | Palias info               -> EcPhlCodeTx.process_alias info
    | Pset info                 -> EcPhlCodeTx.process_set info
    | Prnd (side, info)         -> EcPhlRnd.process_rnd side info
    | Pconseq (opt, info)       -> EcPhlConseq.process_conseq_opt opt info
    | Phrex_elim                -> EcPhlExists.t_hr_exists_elim
    | Phrex_intro fs            -> EcPhlExists.process_exists_intro fs
    | Pexfalso                  -> EcPhlAuto.t_exfalso
    | Pbydeno (mode, info)      -> EcPhlDeno.process_deno mode info
    | PPr pr                    -> EcPhlPr.process_ppr pr
    | Pfel (pos, info)          -> EcPhlFel.process_fel pos info
    | Phoare                    -> EcPhlBdHoare.t_hoare_bd_hoare
    | Pbdhoare_split i          -> EcPhlBdHoare.process_bdhoare_split i
    | Pprbounded                -> EcPhlPr.t_prbounded true
    | Psim info                 -> EcPhlEqobs.process_eqobs_in info
    | Ptrans_stmt info          -> EcPhlTrans.process_equiv_trans info
    | Psymmetry                 -> EcPhlSym.t_equiv_sym
    | Peager_seq infos          -> curry3 EcPhlEager.process_seq infos
    | Peager_if                 -> EcPhlEager.process_if
    | Peager_while info         -> EcPhlEager.process_while info
    | Peager_fun_def            -> EcPhlEager.process_fun_def
    | Peager_fun_abs infos      -> curry EcPhlEager.process_fun_abs infos
    | Peager_call info          -> EcPhlEager.process_call info
    | Peager infos              -> curry EcPhlEager.process_eager infos
    | Pbd_equiv (nm, f1, f2)    -> EcPhlConseq.process_bd_equiv nm (f1, f2)
    | Pauto                     -> EcPhlAuto.t_auto

  in

  try  tx tc
  with (* PHL Specific low errors *)
  | EcLowPhlGoal.InvalidSplit (i, lo, hi) ->
      tc_error_lazy !!tc (fun fmt ->
        Format.fprintf fmt
          "invalid split index: %d is not in the interval [%d..%d]"
          i lo hi)

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
    | Pdo       ((b, n), t) -> `One (process1_do       ttenv (b, n) t)
    | Ptry      t           -> `One (process1_try      ttenv t)
    | Por       (t1, t2)    -> `One (process1_or       ttenv t1 t2)
    | Pseq      ts          -> `One (process1_seq      ttenv ts)
    | Pcase     es          -> `One (process1_case     ttenv es)
    | Pprogress (o, t)      -> `One (process1_progress ttenv o t)
    | Pdebug                -> `One (process1_debug    ttenv)
    | Psubgoal  tt          -> `All (process_chain     ttenv tt)
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
  let tc  = tcenv1_of_proof pf in
  let hd  = FApi.tc1_handle tc in
  let tc  = process1_seq ttenv t tc in
  let hds = FApi.tc_opened tc in
  ((hd, hds), proof_of_tcenv tc)
