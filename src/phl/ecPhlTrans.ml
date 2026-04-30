(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcEnv
open EcPV
open EcMatching
open EcTransMatching
open EcMaps
open EcAst

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
module Low = struct
  (* ------------------------------------------------------------------ *)
  let transitivity_side_cond hyps prml prmr poml pomr p q (p1: ts_inv) (q1: ts_inv) pomt (p2: ts_inv) (q2: ts_inv) =
    let env = LDecl.toenv hyps in
    let cond1 =
      let fv1 = PV.fv env p1.mr p1.inv in
      let fv2 = PV.fv env p2.ml p2.inv in
      let fv  = PV.union fv1 fv2 in
      let elts, glob = PV.ntr_elements fv in
      let m = EcIdent.create "&m" in
      let bd, s = generalize_subst env m elts glob in
      let s1 = PVM.of_mpv s p.mr in
      let s2 = PVM.of_mpv s p.ml in
      let concl = map_ts_inv2 f_and (map_ts_inv1 (PVM.subst env s1) p1) (map_ts_inv1 (PVM.subst env s2) p2) in
      EcSubst.f_forall_mems_ts_inv prml prmr (map_ts_inv2 f_imp p (map_ts_inv1 (f_exists bd) concl)) in
    let cond2 =
      let m2 = LDecl.fresh_id hyps "&m" in
      assert (q.ml = q1.ml && q.mr = q2.mr);
      let q1 = (EcSubst.ts_inv_rebind_right q1 m2).inv in
      let q2 = (EcSubst.ts_inv_rebind_left q2 m2).inv in
      f_forall_mems [poml;(m2,pomt);pomr] (f_imps [q1;q2] q.inv) in
    (cond1, cond2)

  (* ------------------------------------------------------------------ *)
  let t_equivS_trans_r (mt, c2) (p1, q1) (p2, q2) tc =
    let hyps = FApi.tc1_hyps tc in
    let es = tc1_as_equivS tc in
    let m1, m3 = es.es_ml, es.es_mr in
    let cond1, cond2 =
      transitivity_side_cond hyps
        m1 m3 m1 m3 (es_pr es) (es_po es) p1 q1 mt p2 q2 in
    let cond3 =
      f_equivS (snd es.es_ml) mt p1 es.es_sl c2 q1 in
    let cond4 =
      f_equivS mt (snd es.es_mr) p2 c2 es.es_sr q2 in

     FApi.xmutate1 tc `Trans [cond1; cond2; cond3; cond4]

  (* ------------------------------------------------------------------ *)
  let t_equivF_trans_r f (p1, q1) (p2, q2) tc =
    let env, hyps, _ = FApi.tc1_eflat tc in
    let ef = tc1_as_equivF tc in
    let ml, mr = ef.ef_ml, ef.ef_mr in
    let (prml, prmr), (poml, pomr) = Fun.equivF_memenv ml mr ef.ef_fl ef.ef_fr env in
    let (_, pomt) = snd (Fun.hoareF_memenv p1.ml f env) in
    let cond1, cond2 =
      transitivity_side_cond
        hyps prml prmr poml pomr
        (ef_pr ef) (ef_po ef) p1 q1 pomt p2 q2 in
    let cond3 = f_equivF p1 ef.ef_fl f q1 in
    let cond4 = f_equivF p2 f ef.ef_fr q2 in

    FApi.xmutate1 tc `Trans [cond1; cond2; cond3; cond4]
end

(* -------------------------------------------------------------------- *)
let t_equivS_trans = FApi.t_low3 "equiv-trans" Low.t_equivS_trans_r
let t_equivF_trans = FApi.t_low3 "equiv-trans" Low.t_equivF_trans_r

(* -------------------------------------------------------------------- *)
let t_equivS_trans_eq side s tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let c, m, mem_pre = match side with 
    | `Left -> 
      let mem_pre_ss = EcFol.split_sided (fst es.es_ml) (es_pr es) in
      let mem_pre = Option.map (fun mpre -> ss_inv_generalize_right mpre (fst es.es_mr)) mem_pre_ss in
      es.es_sl, es.es_ml, mem_pre
    | `Right -> 
      let mem_pre_ss = EcFol.split_sided (fst es.es_mr) (es_pr es) in
      let mem_pre = Option.map (fun mpre -> ss_inv_generalize_left mpre (fst es.es_ml)) mem_pre_ss in
      es.es_sr, es.es_mr, mem_pre in

  let fv_pr  = EcPV.PV.fv env (fst m) (es_pr es).inv in
  let fv_po  = EcPV.PV.fv env (fst m) (es_po es).inv in
  let fv_r = EcPV.s_read env c in
  let ml, mr = (fst es.es_ml), (fst es.es_mr) in
  let mk_eqs fv =
    let vfv, gfv = EcPV.PV.elements fv in
    let xl x ty = ss_inv_generalize_right (f_pvar x ty ml) mr in
    let xr x ty = ss_inv_generalize_left (f_pvar x ty mr) ml in
    let veq = List.map (fun (x,ty) -> map_ts_inv2 f_eq (xl x ty) (xr x ty)) vfv in
    let geq = List.map (fun mp -> ts_inv_eqglob mp ml mp mr) gfv in
    map_ts_inv ~ml ~mr f_ands (veq @ geq) in
  let pre = mk_eqs (EcPV.PV.union (EcPV.PV.union fv_pr fv_po) fv_r) in
  let pre = map_ts_inv2 f_and pre (odfl {ml=pre.ml;mr=pre.mr;inv=f_true} mem_pre) in
  let post = mk_eqs fv_po in
  let c1, c2 =
    if side = `Left then (pre, post), (es_pr es, es_po es)
    else (es_pr es, es_po es), (pre, post)
  in

  let exists_subtac (tc : tcenv1) =
    (* Ideally these are guaranteed fresh *)
    let pl = EcIdent.create "&p__1" in
    let pr = EcIdent.create "&p__2" in
    let h  = EcIdent.create "__" in
    let tc = EcLowGoal.t_intros_i_1 [pl; pr; h] tc in
    let goal = FApi.tc1_goal tc in

    let p = match side with | `Left -> pl | `Right -> pr in
    let b = match side with | `Left -> true | `Right -> false in

    let handle_exists () =
      (* Pairing up the correct variables for the exists intro *)
      let vs, fm = EcFol.destr_exists goal in
      let eqs_pre, _ =
        let l, r = EcFol.destr_and fm in
        if b then l, r else r, l
      in
      let eqs, _ = destr_and eqs_pre in
      let eqs = destr_ands ~deep:false eqs in
      let doit eq =
        let l, r = EcFol.destr_eq eq in
        let l, r = if b then r, l else l, r in
        let v = EcFol.destr_local l in
        v, r
      in
      let eqs = List.map doit eqs in
      let exvs =
        List.map
          (fun (id, _) ->
            let v = List.assoc id eqs in
            Fsubst.f_subst_mem (EcMemory.memory m) p v)
          vs
      in

      FApi.as_tcenv1 (EcLowGoal.t_exists_intro_s (List.map paformula exvs) tc)
    in

    let tc =
      if EcFol.is_exists goal then
        handle_exists ()
      else
        tc
    in

    FApi.t_seq
      (EcLowGoal.t_generalize_hyp ?clear:(Some `Yes) h)
      EcHiGoal.process_done
      tc
  in

  FApi.t_seqsub
    (t_equivS_trans (EcMemory.memtype m, s) c1 c2)
    [exists_subtac; EcHiGoal.process_done; EcLowGoal.t_id; EcLowGoal.t_id]
    tc

(* -------------------------------------------------------------------- *)
let process_trans_stmt tf s ?pat c tc =
  let hyps = FApi.tc1_hyps tc in
  let es = tc1_as_equivS tc in
  let mt = snd (match s with `Left -> es.es_ml | `Right -> es.es_mr) in

  (* Translation of the stmt *)
  let map =
    match pat with
    | None -> Mstr.empty
    | Some p -> begin
      let regexpstmt = trans_block p in
      let ct = match s with `Left -> es.es_sl | `Right -> es.es_sr in
      match RegexpStmt.search regexpstmt ct.s_node with
      | None -> Mstr.empty
      | Some m -> m
    end
  in
  let c = TTC.tc1_process_prhl_stmt tc s ~map c in

  match tf with
  | TFeq ->
      t_equivS_trans_eq s c tc
  | TFform (p1, q1, p2, q2) ->
    let p1, q1 =
      let ml, mr = fst es.es_ml, fst es.es_mr in
      let hyps = LDecl.push_active_ts es.es_ml (mr, mt) hyps in
      let p1 = TTC.pf_process_form !!tc hyps tbool p1 in
      let q1 = TTC.pf_process_form !!tc hyps tbool q1 in
      {ml;mr;inv=p1}, {ml;mr;inv=q1}
    in
    let p2, q2 =
      let ml, mr = fst es.es_ml, fst es.es_mr in
      let hyps = LDecl.push_active_ts (ml, mt) es.es_mr hyps in
      let p2 = TTC.pf_process_form !!tc hyps tbool p2 in
      let q2 = TTC.pf_process_form !!tc hyps tbool q2 in
      {ml;mr;inv=p2}, {ml;mr;inv=q2} 
    in

    t_equivS_trans (mt, c) (p1, q1) (p2, q2) tc

(* -------------------------------------------------------------------- *)
let process_trans_fun f p1 q1 p2 q2 tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let ef = tc1_as_equivF tc in
  let f = EcTyping.trans_gamepath env f in
  let (_, prmt), (_, pomt) = Fun.hoareF_memenv (EcIdent.create "&dummy") f env in
  let (prml, prmr), (poml, pomr) = Fun.equivF_memenv ef.ef_ml ef.ef_mr ef.ef_fl ef.ef_fr env in
  let process ml mr fo =
    let inv = TTC.pf_process_form !!tc (LDecl.push_active_ts ml mr hyps) tbool fo in
    {ml=fst ml;mr=fst mr;inv} in
  let p1 = process prml (fst prmr, prmt) p1 in
  let q1 = process poml (fst pomr, pomt) q1 in
  let p2 = process (fst prml, prmt) prmr p2 in
  let q2 = process (fst poml, pomt) pomr q2 in
  t_equivF_trans f (p1, q1) (p2, q2) tc

(* -------------------------------------------------------------------- *)
let process_equiv_trans (tk, tf) tc =
  match tk with
  | TKfun f -> begin
    match tf with
    | TFeq ->
      tc_error !!tc "transitivity * does not work on functions"
    | TFform (p1, q1, p2, q2) ->
      process_trans_fun f p1 q1 p2 q2 tc
  end
  | TKstmt (side, stmt) ->
    process_trans_stmt tf side stmt tc
  | TKparsedStmt (side, pat, stmt) ->
    process_trans_stmt tf side ~pat:pat stmt tc
