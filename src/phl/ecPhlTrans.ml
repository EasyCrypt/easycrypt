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

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
module Low = struct
  (* ------------------------------------------------------------------ *)
  let transitivity_side_cond hyps prml prmr poml pomr p q p1 q1 pomt p2 q2 =
    let env = LDecl.toenv hyps in
    let cond1 =
      let fv1 = PV.fv env mright p1 in
      let fv2 = PV.fv env mleft  p2 in
      let fv  = PV.union fv1 fv2 in
      let elts, glob = PV.ntr_elements fv in
      let bd, s = generalize_subst env mhr elts glob in
      let s1 = PVM.of_mpv s mright in
      let s2 = PVM.of_mpv s mleft in
      let concl = f_and (PVM.subst env s1 p1) (PVM.subst env s2 p2) in
      f_forall_mems [prml;prmr] (f_imp p (f_exists bd concl)) in
    let cond2 =
      let m2 = LDecl.fresh_id hyps "&m" in
      let q1 = Fsubst.f_subst_mem mright m2 q1 in
      let q2 = Fsubst.f_subst_mem mleft  m2 q2 in
      f_forall_mems [poml;(m2,pomt);pomr] (f_imps [q1;q2] q) in
    (cond1, cond2)

  (* ------------------------------------------------------------------ *)
  let t_equivS_trans_r (mt, c2) (p1, q1) (p2, q2) tc =
    let hyps = FApi.tc1_hyps tc in
    let es = tc1_as_equivS tc in
    let m1, m3 = es.es_ml, es.es_mr in
    let cond1, cond2 =
      transitivity_side_cond hyps
        m1 m3 m1 m3 es.es_pr es.es_po p1 q1 mt p2 q2 in
    let cond3 =
      f_equivS_r { es with
        es_mr = (mright,mt);
        es_sr = c2;
        es_pr = p1;
        es_po = q1;
      } in
    let cond4 =
      f_equivS_r { es with
        es_ml = (mleft, mt);
        es_sl = c2;
        es_pr = p2;
        es_po = q2;
      } in

     FApi.xmutate1 tc `Trans [cond1; cond2; cond3; cond4]

  (* ------------------------------------------------------------------ *)
  let t_equivF_trans_r f (p1, q1) (p2, q2) tc =
    let env, hyps, _ = FApi.tc1_eflat tc in
    let ef = tc1_as_equivF tc in
    let (prml, prmr), (poml, pomr) = Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
    let (_, pomt) = snd (Fun.hoareF_memenv f env) in
    let cond1, cond2 =
      transitivity_side_cond
        hyps prml prmr poml pomr
        ef.ef_pr ef.ef_po p1 q1 pomt p2 q2 in
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
  let c, m = match side with `Left -> es.es_sl, es.es_ml | `Right -> es.es_sr, es.es_mr in

  let mem_pre = EcFol.split_sided (EcMemory.memory m) es.es_pr in
  let fv_pr  = EcPV.PV.fv env (EcMemory.memory m) es.es_pr in
  let fv_po  = EcPV.PV.fv env (fst m) es.es_po in
  let fv_r = EcPV.s_read env c in
  let mk_eqs fv =
    let vfv, gfv = EcPV.PV.elements fv in
    let veq = List.map (fun (x,ty) -> f_eq (f_pvar x ty mleft) (f_pvar x ty mright)) vfv in
    let geq = List.map (fun mp -> f_eqglob mp mleft mp mright) gfv in
    f_ands (veq @ geq) in
  let pre = mk_eqs (EcPV.PV.union (EcPV.PV.union fv_pr fv_po) fv_r) in
  let pre = f_and pre (odfl f_true mem_pre) in
  let post = mk_eqs fv_po in
  let c1, c2 =
    if side = `Left then (pre, post), (es.es_pr, es.es_po)
    else (es.es_pr, es.es_po), (pre, post)
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
      let hyps = LDecl.push_all [es.es_ml; (mright, mt)] hyps in
      TTC.pf_process_form !!tc hyps tbool p1, TTC.pf_process_form !!tc hyps tbool q1
    in
    let p2, q2 =
      let hyps = LDecl.push_all [(mleft, mt); es.es_mr] hyps in
      TTC.pf_process_form !!tc hyps tbool p2, TTC.pf_process_form !!tc hyps tbool q2
    in
    t_equivS_trans (mt, c) (p1, q1) (p2, q2) tc

(* -------------------------------------------------------------------- *)
let process_trans_fun f p1 q1 p2 q2 tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let ef = tc1_as_equivF tc in
  let f = EcTyping.trans_gamepath env f in
  let (_, prmt), (_, pomt) = Fun.hoareF_memenv f env in
  let (prml, prmr), (poml, pomr) = Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
  let process ml mr fo =
    TTC.pf_process_form !!tc (LDecl.push_all [ml; mr] hyps) tbool fo in
  let p1 = process prml (mright, prmt) p1 in
  let q1 = process poml (mright, pomt) q1 in
  let p2 = process (mleft,prmt) prmr p2 in
  let q2 = process (mleft,pomt) pomr q2 in
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
