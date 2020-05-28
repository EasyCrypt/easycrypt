(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module ER  = EcReduction
module PT  = EcProofTerm
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let pf_destr_eqobsS pf env f =
  let es = destr_equivS f in
  let of_form =
    try  Mpv2.of_form env (fst es.es_ml) (fst es.es_mr)
    with Not_found -> tc_error pf "cannot reconize a set of equalities"
  in
    (es, es.es_sl, es.es_sr, of_form es.es_pr, of_form es.es_po)

(* -------------------------------------------------------------------- *)
let pf_hSS pf hyps h =
  let tH = LDecl.hyp_by_id h hyps in
  (tH, pf_destr_eqobsS pf (LDecl.toenv hyps) tH)

(* -------------------------------------------------------------------- *)
let tc1_destr_eagerS tc s s' =
  let es = tc1_as_equivS tc in
  let c , c' = es.es_sl, es.es_sr in
  let s1, c  = s_split (Zpr.cpos (List.length s.s_node)) c in
  let c',s1' = s_split (Zpr.cpos (List.length c'.s_node - List.length s'.s_node)) c' in

  if not (List.all2 i_equal s1 s.s_node) then begin
    let ppe  = EcPrinting.PPEnv.ofenv (FApi.tc1_env tc) in
    tc_error_lazy !!tc (fun fmt ->
      Format.fprintf fmt
        "the head of the left statement is not of the right form:@\n%a should be@\n%a"
        (EcPrinting.pp_stmt ppe) (stmt s1) (EcPrinting.pp_stmt ppe) s)
  end;

  if not (List.all2 i_equal s1' s'.s_node) then begin
    let ppe  = EcPrinting.PPEnv.ofenv (FApi.tc1_env tc) in
    tc_error_lazy !!tc (fun fmt ->
      Format.fprintf fmt
        "the tail of the right statement is not of the right form:@\n%a should be@\n%a"
        (EcPrinting.pp_stmt ppe) (stmt s1') (EcPrinting.pp_stmt ppe) s')
  end;

  (es, stmt c, stmt c')

(* -------------------------------------------------------------------- *)
(* This ensure condition (d) and (e) of the eager_seq rule.             *)
let pf_compat pf env modS modS' eqR eqIs eqXs =
  if not (Mpv2.subset eqIs eqR) then begin
    let eqR  = Mpv2.to_form mleft mright eqR f_true in
    let eqIs = Mpv2.to_form mleft mright eqIs f_true in
      tc_error_lazy pf (fun fmt ->
        let ppe  = EcPrinting.PPEnv.ofenv env in
        Format.fprintf fmt "%a should be include in %a"
          (EcPrinting.pp_form ppe) eqIs (EcPrinting.pp_form ppe) eqR)
  end;

  let check_pv x1 x2 _ =
    if    not (Mpv2.mem x1 x2 eqXs)
       && (PV.mem_pv env x1 modS || PV.mem_pv env x2 modS')
    then
      tc_error_lazy pf (fun fmt ->
        let ppe = EcPrinting.PPEnv.ofenv env in
        Format.fprintf fmt
          "equality of %a and %a should be ensured by the swapping statement"
          (EcPrinting.pp_pv ppe) x1 (EcPrinting.pp_pv ppe) x2)

  and check_glob m =
    if    not (Mpv2.mem_glob m eqXs)
       && (PV.mem_glob env m modS || PV.mem_glob env m modS')
    then
      tc_error_lazy pf (fun fmt ->
        let ppe = EcPrinting.PPEnv.ofenv env in
        Format.fprintf fmt
          "equality of %a should be ensured by the swapping statement"
          (EcPrinting.pp_topmod ppe) m)

  in
    Mpv2.iter check_pv check_glob eqR

(* -------------------------------------------------------------------- *)
let t_eager_seq_r i j eqR h tc =
  let env, hyps, _ = FApi.tc1_eflat tc in

  (* h is a proof of (h) *)
  let tH, (_, s, s', eqIs, eqXs) = pf_hSS !!tc hyps h in
  let eC, c, c' = tc1_destr_eagerS tc s s' in
  let seqR = Mpv2.of_form env (fst eC.es_ml) (fst eC.es_mr) eqR in

  (* check (d) and (e) *)
  pf_compat !!tc env (s_write env s) (s_write env s') seqR eqIs eqXs;

  let eqO2 = Mpv2.eq_refl (PV.fv env (fst eC.es_mr) eC.es_po) in
  let c1 ,c2  = s_split i c in
  let c1',c2' = s_split j c' in

  let to_form eq =  Mpv2.to_form (fst eC.es_ml) (fst eC.es_mr) eq f_true in

  let a = f_equivS_r { eC with
    es_sl = stmt (s.s_node@c1);
    es_sr = stmt (c1'@s'.s_node);
    es_po = eqR;
  }
  and b = f_equivS_r { eC with
    es_pr = eqR;
    es_sl = stmt (s.s_node@c2);
    es_sr = stmt (c2'@s'.s_node);
  }
  and c = f_equivS_r { eC with
    es_ml = (fst eC.es_ml, snd eC.es_mr);
    es_pr = to_form (Mpv2.eq_fv2 seqR);
    es_sl = stmt c2';
    es_sr = stmt c2';
    es_po = to_form eqO2;
  }

  in

  FApi.t_first
    (t_apply_hyp h)
    (FApi.xmutate1 tc `EagerSeq [tH; a; b; c])

(* -------------------------------------------------------------------- *)
let t_eager_if_r tc =
  let hyps = FApi.tc1_hyps tc in
  let es   = tc1_as_equivS tc in

  let (e , c1 , c2 ), s  = pf_last_if  !!tc es.es_sl in
  let (e', c1', c2'), s' = pf_first_if !!tc es.es_sr in

  let fel = form_of_expr (fst es.es_ml) e in
  let fer = form_of_expr (fst es.es_mr) e' in
  let fe  = form_of_expr mhr e in

  let m2 = as_seq1 (LDecl.fresh_ids hyps ["&m2"]) in

  let aT =
    f_forall
      [(mleft, GTmem (snd es.es_ml)); (mright, GTmem (snd es.es_mr))]
      (f_imp es.es_pr (f_eq fel fer)) in

  let bT =
    let b   = EcIdent.create "b1" in
    let eqb = f_eq fe (f_local b tbool) in
    let sub = Fsubst.f_subst_id in
    let sub = Fsubst.f_bind_mem sub mleft  mhr in
    let sub = Fsubst.f_bind_mem sub mright m2 in
    let p   = Fsubst.f_subst sub es.es_pr in

    f_forall
      [(m2, GTmem (snd es.es_mr)); (b, GTty tbool)]
      (f_hoareS (mhr, snd es.es_ml) (f_and p eqb) s eqb) in

  let cT =
    let pre = f_and es.es_pr (f_eq fel f_true) in
    let st  = stmt (s.s_node @ c1.s_node) in
    let st' = stmt (c1'.s_node @ s'.s_node) in
    f_equivS es.es_ml es.es_mr pre st st' es.es_po in

  let dT =
    let pre = f_and es.es_pr (f_eq fel f_false) in
    let st  = stmt (s.s_node @ c2.s_node) in
    let st' = stmt (c2'.s_node @ s'.s_node) in
    f_equivS es.es_ml es.es_mr pre st st' es.es_po in

  FApi.xmutate1 tc `EagerIf [aT; bT; cT; dT]

(* -------------------------------------------------------------------- *)
let t_eager_while_r h tc =
  let env, hyps, _ = FApi.tc1_eflat tc in

  let tH, (_, s, s', eqIs, eqXs) = pf_hSS !!tc hyps h in
  let eC, wc, wc' = tc1_destr_eagerS tc s s' in

  let (e , c ), n  = pf_first_while !!tc wc  in
  let (e', c'), n' = pf_first_while !!tc wc' in

  if not (List.is_empty n.s_node && List.is_empty n'.s_node) then
    tc_error !!tc "no statements should followed the while loops";

  let to_form eq =  Mpv2.to_form (fst eC.es_ml) (fst eC.es_mr) eq f_true in

  let eqI  = eC.es_pr in
  let seqI =
    try
      Mpv2.of_form env (fst eC.es_ml) (fst eC.es_mr) eqI
    with Not_found ->
      tc_error_lazy !!tc (fun fmt ->
        let ppe  = EcPrinting.PPEnv.ofenv env in
        Format.fprintf fmt "recognize equalities in %a@." (EcPrinting.pp_form ppe) eqI)
  in
  let eqI2 = to_form (Mpv2.eq_fv2 seqI) in
  let e1   = form_of_expr (fst eC.es_ml) e in
  let e2   = form_of_expr (fst eC.es_mr) e' in
  let post = Mpv2.to_form (fst eC.es_ml) (fst eC.es_mr) (Mpv2.union seqI eqXs) (f_not e1) in

  (* check (e) and (f) *)
  pf_compat !!tc env (s_write env s) (s_write env s') seqI eqIs eqXs;

  let aT =
    f_forall
      [mleft,GTmem (snd eC.es_ml); mright, GTmem (snd eC.es_mr)]
      (f_imp eqI (f_eq e1 e2))

  and bT = f_equivS_r { eC with
    es_pr = f_and_simpl eqI e1;
    es_sl = stmt (s.s_node@c.s_node);
    es_sr = stmt (c'.s_node@s'.s_node);
    es_po = eqI;
  }

  and cT = f_equivS_r { eC with
    es_ml = (fst eC.es_ml, snd eC.es_mr);
    es_pr = eqI2;
    es_sl = c';
    es_sr = c';
    es_po = eqI2;
  }

  in

  let tsolve tc =
    FApi.t_first
      (t_apply_hyp h)
      (FApi.xmutate1 tc `EagerWhile [tH; aT; bT; cT])
  in

  FApi.t_seqsub
    (EcPhlConseq.t_equivS_conseq eqI post)
    [t_logic_trivial; t_logic_trivial; tsolve]
    tc

(* -------------------------------------------------------------------- *)
let t_eager_fun_def_r tc =
  let env = FApi.tc1_env tc in
  let eg  = tc1_as_eagerF tc in

  let fl, fr =
    (NormMp.norm_xfun env eg.eg_fl,
     NormMp.norm_xfun env eg.eg_fr)
  in

  EcPhlFun.check_concrete !!tc env fl;
  EcPhlFun.check_concrete !!tc env fr;

  let (memenvl, (fsigl,fdefl),
       memenvr, (fsigr,fdefr), env) = Fun.equivS fl fr env in

  let extend mem fdef =
    match fdef.f_ret with
    | None -> f_tt, mem, fdef.f_body
    | Some e ->
      let v = {v_name = "result"; v_type = e.e_ty } in
      let mem, s = EcLowPhlGoal.fresh_pv mem v in
      let f = EcMemory.xpath mem in
      let x = EcTypes.pv_loc f s in
      f_pvar x e.e_ty (fst mem), mem,
      s_seq fdef.f_body (stmt [i_asgn(LvVar(x,e.e_ty), e)])
  in

  let el, meml, sfl = extend memenvl fdefl in
  let er, memr, sfr = extend memenvr fdefr in
  let ml, mr = EcMemory.memory meml, EcMemory.memory memr in
  let s = PVM.empty in
  let s = PVM.add env (pv_res fl) ml el s in
  let s = PVM.add env (pv_res fr) mr er s in
  let post = PVM.subst env s eg.eg_po in
  let s = PVM.empty in
  let s = EcPhlFun.subst_pre env fl fsigl ml s in
  let s = EcPhlFun.subst_pre env fr fsigr mr s in
  let pre = PVM.subst env s eg.eg_pr in

  let cond = f_equivS_r {
    es_ml = meml;
    es_mr = memr;
    es_sl = s_seq eg.eg_sl sfl;
    es_sr = s_seq sfr eg.eg_sr;
    es_pr = pre;
    es_po = post;
  } in

  FApi.xmutate1 tc `EagerFunDef [cond]

(* -------------------------------------------------------------------- *)
let t_eager_fun_abs_r eqI h tc =
  let env, hyps, _ = FApi.tc1_eflat tc in

  let tH, (_, s, s', eqIs, eqXs) = pf_hSS !!tc hyps h in
  let eg = tc1_as_eagerF tc in

  if not (s_equal s eg.eg_sl && s_equal s' eg.eg_sr) then
    tc_error !!tc "cannot reconize the swapping statement";

  let fl, fr = eg.eg_fl, eg.eg_fr in
  let pre, post, sg =
    EcPhlFun.FunAbsLow.equivF_abs_spec !!tc env fl fr eqI in

  let do1 og sg =
    let ef = destr_equivF og in
    let torefl f =
      Mpv2.to_form mleft mright
        (Mpv2.eq_refl (PV.fv env mright f))
        f_true
    in
         f_eagerF ef.ef_pr s ef.ef_fl ef.ef_fr s' ef.ef_po
      :: f_equivF (torefl ef.ef_pr) ef.ef_fr ef.ef_fr (torefl ef.ef_po)
      :: sg
  in

  let sg   = List.fold_right do1 sg [] in
  let seqI = Mpv2.of_form env mleft mright eqI in

  (* check (e) and (f)*)
  pf_compat !!tc env (s_write env s) (s_write env s') seqI eqIs eqXs;

  (* TODO : check that S S' do not modify glob A *)
  let tactic tc =
    FApi.t_first (t_apply_hyp h)
      (FApi.xmutate1 tc `EagerFunAbs (tH::sg))
  in

  FApi.t_last tactic (EcPhlConseq.t_eagerF_conseq pre post tc)

(* -------------------------------------------------------------------- *)
let t_eager_call_r fpre fpost tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let es = tc1_as_equivS tc in

  let (lvl, fl, argsl), sl = pf_last_call  !!tc es.es_sl in
  let (lvr, fr, argsr), sr = pf_first_call !!tc es.es_sr in

  let swl = s_write env sl in
  let swr = s_write env sr in

  let check_a e =
    let er   = e_read env e in
    let diff = PV.interdep env swl er in

    if not (PV.is_empty diff) then
      tc_error_lazy !!tc (fun fmt ->
        Format.fprintf fmt
          "eager call: the statement write %a"
          (PV.pp env) diff)
  in

  List.iter check_a argsl;

  let ml = EcMemory.memory es.es_ml in
  let mr = EcMemory.memory es.es_mr in
  let modil = PV.union (f_write env fl) swl in
  let modir = PV.union (f_write env fr) swr in
  let post  = EcPhlCall.wp2_call env fpre fpost (lvl, fl, argsl) modil

     (lvr,fr,argsr) modir ml mr es.es_po hyps in
  let f_concl = f_eagerF fpre sl fl fr sr fpost in
  let concl   = f_equivS_r { es with es_sl = stmt []; es_sr = stmt []; es_po = post; } in

  FApi.xmutate1 tc `EagerCall [f_concl; concl]

(* -------------------------------------------------------------------- *)
let check_only_global pf env s =
  let sw = s_write env s in
  let sr = s_read  env s in

  let check_glob v _ =
    if is_loc v then
      tc_error_lazy pf (fun fmt ->
        let ppe = EcPrinting.PPEnv.ofenv env in
        Format.fprintf fmt
          "swapping statement should use only global variables: %a"
          (EcPrinting.pp_pv ppe) v)
  in

  let check_mp _ = () in

  PV.iter check_glob check_mp sw;
  PV.iter check_glob check_mp sr

(* -------------------------------------------------------------------- *)
(* This part of the code is for automatic application of eager rules    *)
(* -------------------------------------------------------------------- *)
let eager pf env s s' inv eqIs eqXs c c' eqO =
  let modi  = s_write env s in
  let modi' = s_write env s' in
  let readi = s_read env s in

  let rev st = List.rev st.s_node in

  let check_args args =
    let read = List.fold_left (e_read_r env) PV.empty args in
    if not (PV.indep env modi read) then raise EqObsInError in

  let check_swap_s i =
    let m = is_write env [i] in
    let r = is_read  env [i] in
    let t =
         PV.indep env m modi
      && PV.indep env m readi
      && PV.indep env modi r
    in
      if not t then raise EqObsInError
  in

  let remove lvl lvr eqs =
    let aux eqs (pvl, tyl) (pvr, tyr) =
      if   (ER.EqTest.for_type env tyl tyr)
      then Mpv2.remove env pvl pvr eqs
      else raise EqObsInError in

    match lvl, lvr with
    | LvVar xl, LvVar xr -> aux eqs xl xr

    | LvTuple ll, LvTuple lr
        when List.length ll = List.length lr
      ->
        List.fold_left2 aux eqs ll lr

    | _, _ -> raise EqObsInError in

  let oremove lvl lvr eqs =
    match lvl, lvr with
    | None    , None     -> eqs
    | Some lvl, Some lvr -> remove lvl lvr eqs
    | _       , _        -> raise EqObsInError in

  let rec s_eager fhyps rsl rsr eqo =
    match rsl, rsr with
    | [], _  -> [], rsr, fhyps, eqo
    | _ , [] -> rsl, [], fhyps, eqo

    | il::rsl', ir::rsr' ->
      match (try Some (i_eager fhyps il ir eqo) with _ -> None) with
      | None -> rsl, rsr, fhyps, eqo
      | Some (fhyps, eqi) ->
        (* we ensure that the seq rule can be apply *)
        let eqi2 = i_eqobs_in_refl env ir (Mpv2.fv2 eqo) in
        if not (PV.subset eqi2 (Mpv2.fv2 eqi)) then raise EqObsInError;
        pf_compat pf env modi modi' eqi eqIs eqXs;
        s_eager fhyps rsl' rsr' eqi

  and i_eager fhyps il ir eqo =
    match il.i_node, ir.i_node with
    | Sasgn (lvl, el), Sasgn (lvr, er)
    | Srnd  (lvl, el), Srnd  (lvr, er) ->
        check_swap_s il;
        let eqnm = Mpv2.split_nmod env modi modi' eqo in
        let eqm  = Mpv2.split_mod env modi modi' eqo in
        if not (Mpv2.subset eqm eqXs) then raise EqObsInError;
        let eqi = Mpv2.union eqIs eqnm in
        (fhyps, Mpv2.add_eqs env el er (remove lvl lvr eqi) )

    | Scall (lvl, fl, argsl), Scall (lvr, fr, argsr)
        when List.length argsl = List.length argsr
      ->
        check_args argsl;
        let eqo  = oremove lvl lvr eqo in
        let modl = PV.union modi (f_write env fl) in
        let modr = PV.union modi' (f_write env fr) in
        let eqnm = Mpv2.split_nmod env modl modr eqo in
        let outf = Mpv2.split_mod  env modl modr eqo in
        Mpv2.check_glob outf;
        let fhyps, inf = f_eager fhyps fl fr outf in
        let eqi =
          List.fold_left2
            (fun eqs e1 e2 -> Mpv2.add_eqs env e1 e2 eqs)
            (Mpv2.union eqnm inf) argsl argsr
        in
          (fhyps, eqi)

    | Sif (el, stl, sfl), Sif (er, str, sfr) ->
        check_args [el];
        let r1,r2,fhyps1, eqs1 = s_eager fhyps (rev stl) (rev str) eqo in
        if r1 <> [] || r2 <> [] then raise EqObsInError;
        let r1,r2, fhyps2, eqs2 = s_eager fhyps1 (rev sfl) (rev sfr) eqo in
        if r1 <> [] || r2 <> [] then raise EqObsInError;
        let eqi = Mpv2.union eqs1 eqs2 in
        let eqe = Mpv2.add_eqs env el er eqi in
        (fhyps2, eqe)

    | Swhile (el, sl), Swhile (er, sr2) ->
        check_args [el]; (* ensure condition (d) *)
        let sl, sr = rev sl, rev sr2 in
        let rec aux eqo =
          let r1,r2,fhyps, eqi = s_eager fhyps sl sr eqo in
          if r1 <> [] || r2 <> [] then raise EqObsInError;
          if Mpv2.subset eqi eqo then fhyps, eqo
          else aux (Mpv2.union eqi eqo)
        in
        let fhyps, eqi = aux (Mpv2.union eqIs (Mpv2.add_eqs env el er eqo)) in
        (* by construction condition (a), (b) and (c) are satisfied *)
        pf_compat pf env modi modi' eqi eqIs eqXs; (* ensure (e) and (f) *)
        (* (h) is assumed *)
        (fhyps, eqi)

    | Sassert el, Sassert er ->
        check_args [el];
        let eqnm = Mpv2.split_nmod env modi modi' eqo in
        let eqm  = Mpv2.split_mod  env modi modi' eqo in
        if not (Mpv2.subset eqm eqXs) then raise EqObsInError;
        let eqi = Mpv2.union eqIs eqnm in
        (fhyps, Mpv2.add_eqs env el er eqi)

    | Sabstract _, Sabstract _ -> assert false (* FIXME *)

    | _, _ -> raise EqObsInError

  and f_eager fhyps fl fr out =
    let fl = NormMp.norm_xfun env fl in
    let fr = NormMp.norm_xfun env fr in

    let rec aux fhyps =
      match fhyps with
      | [] -> [fl,fr,out]
      | (fl', fr', out') :: fhyps ->
        if   EcPath.x_equal fl fl' && EcPath.x_equal fr fr'
        then (fl ,fr , Mpv2.union out out') :: fhyps
        else (fl',fr', out') :: (aux fhyps)
    in
      aux fhyps, inv
  in

  s_eager [] (rev c) (rev c') eqO

(* -------------------------------------------------------------------- *)
let t_eager_r h inv tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let _, (_, s, s', eqIs, eqXs) = pf_hSS !!tc hyps h in

  check_only_global !!tc env s;
  check_only_global !!tc env s';

  let eC, c, c' = tc1_destr_eagerS tc s s' in
  let eqinv = Mpv2.of_form env mleft mright inv in
  let eqO = Mpv2.of_form env mleft mright eC.es_po in
  let c1, c1', fhyps, eqi = eager !!tc env s s' eqinv eqIs eqXs c c' eqO in

  if c1 <> [] || c1' <> [] then
    tc_error !!tc "not able to apply eager"; (* FIXME *)

  let dof (fl,fr,eqo) =
    let defl = Fun.by_xpath fl env in
    let defr = Fun.by_xpath fr env in
    let sigl, sigr = defl.f_sig, defr.f_sig in
    let eq_res = f_eqres fl sigl.fs_ret mleft fr sigr.fs_ret mright in
    let post = Mpv2.to_form mleft mright eqo eq_res in
    let eq_params =
      f_eqparams
        fl sigl.fs_arg sigl.fs_anames mleft
        fr sigr.fs_arg sigr.fs_anames mright in
    let pre = f_and_simpl eq_params inv in
    f_eagerF pre s fl fr s' post
  in

  let concl =
    f_equivS_r { eC with
      es_sl = stmt []; es_sr = stmt [];
      es_po = Mpv2.to_form mleft mright eqi f_true;
    }
  in

  let concls = List.map dof fhyps in

  FApi.xmutate1 tc `EagerAuto (concl::concls)

(* -------------------------------------------------------------------- *)
let t_eager_seq     = FApi.t_low4 "eager-seq"     t_eager_seq_r
let t_eager_if      = FApi.t_low0 "eager-if"      t_eager_if_r
let t_eager_while   = FApi.t_low1 "eager-while"   t_eager_while_r
let t_eager_fun_def = FApi.t_low0 "eager-fun-def" t_eager_fun_def_r
let t_eager_fun_abs = FApi.t_low2 "eager-fun-abs" t_eager_fun_abs_r
let t_eager_call    = FApi.t_low2 "eager-call"    t_eager_call_r
let t_eager         = FApi.t_low2 "eager"         t_eager_r

(* -------------------------------------------------------------------- *)
let process_info info tc =
  let env,hyps,_ = FApi.tc1_eflat tc in

  match info with
  | EcParsetree.LE_done h ->
      (t_id tc, fst (LDecl.hyp_by_name (unloc h) hyps))

  | EcParsetree.LE_todo (h, s1, s2, eqIs, eqXs) ->
    let ml,mr =
      match (FApi.tc1_goal tc).f_node with
      | FeagerF _ ->
        EcEnv.Fun.inv_memory `Left env, EcEnv.Fun.inv_memory `Right env
      | _ ->
        let es    = tc1_as_equivS tc in
        es.es_ml, es.es_mr in
    let hyps = LDecl.push_all [ml; mr] hyps in
    let process_formula = TTC.pf_process_form !!tc hyps tbool in
    let eqIs  = process_formula eqIs in
    let eqXs  = process_formula eqXs in
    let s1    = TTC.tc1_process_stmt tc (snd ml) s1 in
    let s2    = TTC.tc1_process_stmt tc (snd mr) s2 in
    let f     = f_equivS ml mr eqIs s1 s2 eqXs in
    let h     = LDecl.fresh_id hyps (unloc h) in
    (FApi.t_last (t_intros_i [h]) (t_cut f tc), h)

(* -------------------------------------------------------------------- *)
let process_seq info (i, j) eqR tc =
  let eqR   = TTC.tc1_process_prhl_form tc tbool eqR in
  let gs, h = process_info info tc in
  FApi.t_last (t_eager_seq i j eqR h) gs

(* -------------------------------------------------------------------- *)
let process_if tc =
  t_eager_if tc

(* -------------------------------------------------------------------- *)
let process_while info tc =
  let gs, h = process_info info tc in
  FApi.t_last (t_eager_while h) gs

(* -------------------------------------------------------------------- *)
let process_fun_def tc =
  t_eager_fun_def tc

(* -------------------------------------------------------------------- *)
let process_fun_abs info eqI tc =
  let hyps  = FApi.tc1_hyps tc in
  let env   = LDecl.inv_memenv hyps in
  let eqI   = TTC.pf_process_form !!tc env tbool eqI in
  let gs, h = process_info info tc in
  FApi.t_last (t_eager_fun_abs eqI h) gs

(* -------------------------------------------------------------------- *)
let process_call info tc =
  let process_cut info =
    match info with
    | EcParsetree.CI_spec (fpre, fpost) ->
        let env, hyps, _ = FApi.tc1_eflat tc in
        let es  = tc1_as_equivS tc in

        let (_,fl,_), sl = tc1_last_call  tc es.es_sl in
        let (_,fr,_), sr = tc1_first_call tc es.es_sr in

        check_only_global !!tc env sl;
        check_only_global !!tc env sr;

        let penv, qenv = LDecl.equivF fl fr hyps in
        let fpre  = TTC.pf_process_form !!tc penv tbool fpre  in
        let fpost = TTC.pf_process_form !!tc qenv tbool fpost in
        f_eagerF fpre sl fl fr sr fpost

    | _ -> tc_error !!tc "invalid arguments"
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut ~prcut:process_cut tc info in
  let eg = pf_as_eagerF !!tc ax in

  FApi.t_on1seq 0
    (t_eager_call eg.eg_pr eg.eg_po)
    (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt)
    tc

(* -------------------------------------------------------------------- *)
let process_eager info inv tc =
  let hyps  = FApi.tc1_hyps tc in
  let penv  = LDecl.inv_memenv hyps in
  let inv   = TTC.pf_process_formula !!tc penv inv in
  let gs, h = process_info info tc in
  FApi.t_last (t_eager h inv) gs
