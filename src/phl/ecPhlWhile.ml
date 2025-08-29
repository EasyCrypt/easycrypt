(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcTypes
open EcFol
open EcModules
open EcPV
open EcParsetree

open EcCoreGoal
open EcLowPhlGoal
open EcLowGoal

module Sx  = EcPath.Sx
module TTC = EcProofTyping
module EP  = EcParsetree
module Mid = EcIdent.Mid


(* -------------------------------------------------------------------- *)
let while_info env e s =
  let rec i_info (w,r,c) i =
    match i.i_node with
    | Sasgn(lp, e) | Srnd(lp, e) ->
        let r = e_read_r env r e in
        let w = lp_write_r env w lp in
        (w, r, c)

    | Sif (e, s1, s2) ->
        let r = e_read_r env r e in s_info (s_info (w, r, c) s1) s2

    | Swhile (e, s) ->
        let r = e_read_r env r e in s_info (w, r, c) s

    | Smatch (e, bs) ->
        let r = e_read_r env r e in
        List.fold_left (fun st (_, b) -> s_info st b) (w, r, c) bs

    | Scall (lp, f, es) ->
        let r = List.fold_left (e_read_r env) r es in
        let w = match lp with None -> w | Some lp -> lp_write_r env w lp in
        let f = EcEnv.NormMp.norm_xfun env f in
        (w, r, Sx.add f c)

    | Sassert e ->
        (w, e_read_r env r e, c)

    | Sabstract id ->
        let add_pv x (pv,ty) = PV.add env pv ty x in
        let us = EcEnv.AbsStmt.byid id env in
        let w = List.fold_left add_pv w us.EcModules.aus_writes in
        let r = List.fold_left add_pv r us.EcModules.aus_reads in
        let c = List.fold_left (fun c f -> Sx.add f c) c us.EcModules.aus_calls in
        (w, r, c)

  and s_info info s = List.fold_left i_info info s.s_node in

  let (w,r,c) = s_info (PV.empty, EcPV.e_read env e, Sx.empty) s in

  { EcModules.aus_reads  = fst (PV.ntr_elements r);
    EcModules.aus_writes = fst (PV.ntr_elements w);
    EcModules.aus_calls  = Sx.ntr_elements c; }

(* -------------------------------------------------------------------- *)
let t_hoare_while_r inv tc =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_hoareS tc in
  let (e, c), s = tc1_last_while tc hs.hs_s in
  let (m, mt) = hs.hs_m in
  let e = ss_inv_of_expr m e in
  (* the body preserves the invariant *)
  let b_pre  = map_ss_inv2 f_and_simpl inv e in
  let b_post = inv in
  let b_concl = f_hoareS mt b_pre c b_post in
  (* the wp of the while *)
  let f_imps_simpl' f = f_imps_simpl (List.tl f) (List.hd f) in
  let post = map_ss_inv f_imps_simpl' [hs_po hs;map_ss_inv1 f_not_simpl e; inv]  in
  let modi = s_write env c in
  let post = generalize_mod_ss_inv env modi post in
  let post = map_ss_inv2 f_and_simpl inv post in
  let concl = f_hoareS mt (hs_pr hs) s post in

  FApi.xmutate1 tc `While [b_concl; concl]

(* -------------------------------------------------------------------- *)
let check_single_stmt tc s =
  if not (List.is_empty s.s_node) then
    tc_error !!tc  "only single loop statements are accepted"

let t_ehoare_while_core tc =
  let hyps = FApi.tc1_hyps tc in
  let hs = tc1_as_ehoareS tc in
  let (e, c), s = tc1_last_while tc hs.ehs_s in
  check_single_stmt tc s;
  let (m, mt) = hs.ehs_m in
  let e = ss_inv_of_expr m e in
  if not (EcReduction.ss_inv_alpha_eq hyps (ehs_po hs) 
      (map_ss_inv2 f_interp_ehoare_form (map_ss_inv1 f_not e) (ehs_pr hs))) then
    tc_error !!tc "ehoare while rule: wrong post-condition";
  (* the body preserves the invariant *)
  let b_pre  = map_ss_inv2 f_interp_ehoare_form e (ehs_pr hs) in
  let b_concl = f_eHoareS mt b_pre c (ehs_pr hs) in
  FApi.xmutate1 tc `While [b_concl]

let t_ehoare_while inv tc =
  let hs = tc1_as_ehoareS tc in
  let (e,_), _ = tc1_last_while tc hs.ehs_s in
  let m = EcMemory.memory hs.ehs_m in
  let e = ss_inv_of_expr m e in
  let tc =
    FApi.t_rotate `Left 1 (EcPhlApp.t_ehoare_app (0, `ByPos (List.length hs.ehs_s.s_node - 1)) inv tc) in
  FApi.t_sub
    [(EcPhlConseq.t_ehoareS_conseq inv (map_ss_inv2 f_interp_ehoare_form (map_ss_inv1 f_not e) inv)) @+
       [t_trivial;
        t_id;
        t_ehoare_while_core ];
     t_id] tc

(* -------------------------------------------------------------------- *)
(* rule >=, <=, =, with a stricly decreasing variant *)
let t_bdhoare_while_r inv vrnt tc =
  let env = FApi.tc1_env tc in
  let bhs = tc1_as_bdhoareS tc in
  let (e, c), s = tc1_last_while tc bhs.bhs_s in
  let (m, mt) = bhs.bhs_m in
  let e = ss_inv_of_expr m e in
  (* the body preserves the invariant *)
  let k_id = EcIdent.create "z" in
  let k = {m;inv=f_local k_id tint} in
  let vrnt_eq_k = map_ss_inv2 f_eq vrnt k in
  let vrnt_lt_k = map_ss_inv2 f_int_lt vrnt k in
  let b_pre  = map_ss_inv2 f_and_simpl (map_ss_inv2 f_and_simpl inv e) vrnt_eq_k in
  let b_post = map_ss_inv2 f_and_simpl inv vrnt_lt_k in
  let b_concl = f_bdHoareS mt b_pre c b_post FHeq {m;inv=f_r1} in
  let b_concl = f_forall_simpl [(k_id,GTty tint)] b_concl in
  (* the wp of the while *)
  let f_imps_simpl' f = f_imps_simpl (List.tl f) (List.hd f) in
  let post = map_ss_inv f_imps_simpl' [bhs_po bhs; map_ss_inv1 f_not_simpl e; inv] in
  let term_condition = map_ss_inv f_imps_simpl' 
    [map_ss_inv1 f_not_simpl e; inv;map_ss_inv2 f_int_le vrnt {m;inv=f_i0}] in
  let post = map_ss_inv2 f_and term_condition post in
  let modi = s_write env c in
  let post = generalize_mod_ss_inv env modi post in
  let post = map_ss_inv2 f_and_simpl inv post in
  let concl = f_bdHoareS mt (bhs_pr bhs) s post bhs.bhs_cmp (bhs_bd bhs) in

  FApi.xmutate1 tc `While [b_concl; concl]

(* -------------------------------------------------------------------- *)
(* Rule for <= *)
let t_bdhoare_while_rev_r inv tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let bhs = tc1_as_bdhoareS tc in

  if bhs.bhs_cmp <> FHle then
    tc_error !!tc "only judgments with an upper-bounded are supported";

  let b_pre  = (bhs_pr bhs) in
  let b_post = (bhs_po bhs) in
  let mem    = bhs.bhs_m in
  let (m, mt) = mem in
  let bound  = (bhs_bd bhs) in

  let (lp_guard_exp, lp_body), rem_s = tc1_last_while tc bhs.bhs_s in
  let lp_guard = ss_inv_of_expr (EcMemory.memory mem) lp_guard_exp in

  let w_u   = while_info env lp_guard_exp lp_body in
  let w     = EcEnv.LDecl.fresh_id hyps "w" in
  let hyps' = EcEnv.LDecl.add_local w (EcBaseLogic.LD_abs_st w_u) hyps in

  (* 1. Sub-goal *)
  let body_concl =
    let while_s  = EcModules.stmt [EcModules.i_abstract w] in
    let unfolded_while_s = EcModules.s_seq lp_body while_s in
    let while_jgmt = f_bdHoareS mt inv while_s (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs) in
    let unfolded_while_jgmt = f_bdHoareS
      mt (map_ss_inv2 f_and inv lp_guard) unfolded_while_s (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs)
    in
      f_imp while_jgmt unfolded_while_jgmt
  in

  (* 2. Sub-goal *)
  let rem_concl =
    let modi = s_write env lp_body in
    let term_post = map_ss_inv2 f_imp
      (map_ss_inv2 f_and inv (map_ss_inv2 f_and (map_ss_inv1 f_not lp_guard) b_post))
      (map_ss_inv2 f_eq bound {m;inv=f_r1}) in
    let term_post = generalize_mod_ss_inv env modi term_post in
    let term_post = map_ss_inv2 f_and inv term_post in
    f_hoareS mt b_pre rem_s term_post
  in

  FApi.xmutate1_hyps tc `While [(hyps', body_concl); (hyps, rem_concl)]

(* -------------------------------------------------------------------- *)
(* Rule for = or >= *)

let t_bdhoare_while_rev_geq_r inv vrnt k (eps: ss_inv) tc =
  let env, hyps, _ = FApi.tc1_eflat tc in

  let bhs = tc1_as_bdhoareS tc in

  if bhs.bhs_cmp = FHle then
    tc_error !!tc "only judgments with an lower/eq-bounded are supported";

  let b_pre  = bhs_pr bhs in
  let b_post = bhs_po bhs in
  let mem    = bhs.bhs_m in
  let (m, mt) = mem in

  let (lp_guard_exp, lp_body), rem_s = tc1_last_while tc bhs.bhs_s in

  if not (PV.indep env (s_write env lp_body) (PV.fv env (EcMemory.memory mem) eps.inv)) then
    tc_error !!tc
      "The variant decreasing rate lower-bound cannot "
      "depend on variables written by the loop body";

  check_single_stmt tc rem_s;

  let lp_guard = ss_inv_of_expr m lp_guard_exp in
  let bound    = bhs_bd bhs in
  let modi     = s_write env lp_body in

  (* 1. Pre-invariant *)
  let pre_inv_concl = EcSubst.f_forall_mems_ss_inv mem (map_ss_inv2 f_imp b_pre inv) in

  (* 2. Pre-bound *)
  let pre_bound_concl =
    let term_post = [b_pre; map_ss_inv1 f_not lp_guard] in
    let concl =
      if bhs.bhs_cmp = FHeq then
        map_ss_inv2 f_eq bound (map_ss_inv3 f_if b_post {m;inv=f_r1} {m;inv=f_r0})
      else map_ss_inv2 f_imp (map_ss_inv1 f_not b_post) (map_ss_inv2 f_eq bound {m;inv=f_r0}) in
    let f_imps' f = f_imps (List.tl f) (List.hd f) in
    let term_post = map_ss_inv f_imps' (concl::term_post) in
    let term_post = generalize_mod_ss_inv env modi term_post in
      EcSubst.f_forall_mems_ss_inv mem term_post
  in

  (* 3. Term-invariant *)
  let inv_term_concl =
    let concl = map_ss_inv2 f_imp (map_ss_inv2 f_int_le vrnt {m;inv=f_i0}) (map_ss_inv1 f_not lp_guard) in
    let concl = map_ss_inv2 f_and (map_ss_inv2 f_int_le vrnt k) concl in
    let concl = map_ss_inv2 f_imp inv concl in
      EcSubst.f_forall_mems_ss_inv mem (generalize_mod_ss_inv env modi concl)
  in

  (* 4. Vrnt conclusion *)
  let vrnt_concl =
    let k_id = EcIdent.create "z" in
    let k    = {m;inv=f_local k_id tint} in
    let vrnt_eq_k = map_ss_inv2 f_eq vrnt k in
    let vrnt_lt_k = map_ss_inv2 f_int_lt vrnt k in
      f_and
        (EcSubst.f_forall_mems_ss_inv mem (map_ss_inv2 f_imp inv 
          (map_ss_inv2 f_real_lt {m;inv=f_r0} eps)))
        (f_forall_simpl [(k_id,GTty tint)]
           (f_bdHoareS
              mt 
              (map_ss_inv f_ands [inv;lp_guard;vrnt_eq_k]) 
              lp_body
              vrnt_lt_k 
              FHge
              eps))
  in

  (* 5. Out invariant *)
  let inv_concl =
    f_bdHoareS mt (map_ss_inv2 f_and inv lp_guard) lp_body inv FHeq {m;inv=f_r1}
  in

  (* 6. Out body *)
  let w_u = while_info env lp_guard_exp lp_body in
  let w   = EcEnv.LDecl.fresh_id hyps "w" in
  let hyps' = EcEnv.LDecl.add_local w (EcBaseLogic.LD_abs_st w_u) hyps in

  let body_concl =
    let while_s1 = EcModules.stmt [EcModules.i_abstract w] in

    let unfolded_while_s = EcModules.s_seq lp_body while_s1 in
    let while_jgmt = f_bdHoareS mt b_pre while_s1 (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs) in
    let unfolded_while_jgmt = f_bdHoareS
      mt (map_ss_inv2 f_and b_pre lp_guard) unfolded_while_s (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs)
    in
    f_imp while_jgmt unfolded_while_jgmt
  in

  FApi.xmutate1_hyps tc `While
    [(hyps , pre_inv_concl  );
     (hyps , pre_bound_concl);
     (hyps , inv_term_concl );
     (hyps', body_concl     );
     (hyps , inv_concl      );
     (hyps , vrnt_concl     )]

(* -------------------------------------------------------------------- *)
let t_equiv_while_disj_r side vrnt inv tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let ss_inv_generalize_other f = 
    match side with
    | `Left  -> ss_inv_generalize_right f (fst es.es_mr)
    | `Right -> ss_inv_generalize_left f (fst es.es_ml) in
  let ts_inv_lower_side2 = sideif side ts_inv_lower_left2 ts_inv_lower_right2 in
  let generalize_mod_side = sideif side generalize_mod_left generalize_mod_right in
  let s, m_side, m_other =
    match side with
    | `Left  -> es.es_sl, es.es_ml, es.es_mr
    | `Right -> es.es_sr, es.es_mr, es.es_ml in
  let (ml, mr) = (fst es.es_ml, fst es.es_mr) in
  let (e, c), s = tc1_last_while tc s in
  let e = ss_inv_of_expr (EcMemory.memory m_side) e in
  let e = ss_inv_generalize_other e in

  (* 1. The body preserves the invariant and the variant decreases. *)
  let k_id = EcIdent.create "z" in
  let k    = {ml;mr;inv=f_local k_id tint} in

  let vrnt_eq_k = map_ts_inv2 f_eq vrnt k in
  let vrnt_lt_k = map_ts_inv2 f_int_lt vrnt k in

  let b_pre   = map_ts_inv2 f_and_simpl (map_ts_inv2 f_and_simpl inv e) vrnt_eq_k in
  let b_post  = map_ts_inv2 f_and_simpl inv vrnt_lt_k in
  let b_concl = ts_inv_lower_side2 (fun pr po -> 
    let m = EcIdent.create "&hr" in
    let pr = EcSubst.ss_inv_rebind pr m in
    let po = EcSubst.ss_inv_rebind po m in
    f_bdHoareS (snd m_side) pr c po FHeq {m;inv=f_r1}) b_pre b_post in
  let b_concl = map_ss_inv1 (f_forall_simpl [(k_id,GTty tint)]) b_concl in
  let b_concl = EcSubst.f_forall_mems_ss_inv (EcIdent.create "&m", snd m_other) b_concl in

  (* 2. WP of the while *)
  let f_imps_simpl' fl = f_imps_simpl (List.tl fl) (List.hd fl) in
  let post = map_ts_inv f_imps_simpl' [es_po es; map_ts_inv1 f_not_simpl e; inv] in
  let term_condition = map_ts_inv 
    f_imps_simpl' [map_ts_inv1 f_not_simpl e; inv;map_ts_inv2 f_int_le vrnt {ml;mr;inv=f_i0}] in
  let post = map_ts_inv2 f_and term_condition post in
  let modi = s_write env c in
  let post = generalize_mod_side env modi post in
  let post = map_ts_inv2 f_and_simpl inv post in
  let concl =
    match side with
    | `Left  -> f_equivS (snd es.es_ml) (snd es.es_mr) (es_pr es) s es.es_sr post
    | `Right -> f_equivS (snd es.es_ml) (snd es.es_mr) (es_pr es) es.es_sl s post
  in

  FApi.xmutate1 tc `While [b_concl; concl]

(* -------------------------------------------------------------------- *)
module LossLess = struct
  exception CannotTranslate

  let form_of_expr env mother mh =
    let map = ref (Mid.add mother (EcPV.PVMap.create env) Mid.empty) in

    let rec aux fp =
      match fp.f_node with
      | Fint   z -> e_int z
      | Flocal x -> e_local x fp.f_ty

      | Fop  (p, tys) -> e_op p tys fp.f_ty
      | Fapp (f, fs)  -> e_app (aux f) (List.map aux fs) fp.f_ty
      | Ftuple fs     -> e_tuple (List.map aux fs)
      | Fproj  (f, i) -> e_proj (aux f) i fp.f_ty

      | Fif (c, f1, f2) ->
         e_if (aux c) (aux f1) (aux f2)

      | Fmatch (c, bs, ty) ->
         e_match (aux c) (List.map aux bs) ty

      | Flet (lp, f1, f2) ->
         e_let lp (aux f1) (aux f2)

      | Fquant (kd, bds, f) ->
         e_quantif (auxkd kd) (List.map auxbd bds) (aux f)

      | Fpvar (pv, m) ->
         if EcIdent.id_equal m mh then
           e_var pv fp.f_ty
         else
           let bds = odfl (EcPV.PVMap.create env) (Mid.find_opt m !map) in
           let idx =
             match EcPV.PVMap.find pv bds with
             | None ->
                 let pfx = EcIdent.name m in
                 let pfx = String.sub pfx  1 (String.length pfx - 1) in
                 let x   = symbol_of_pv pv in
                 let x   = EcIdent.create (x ^ "_" ^ pfx) in
                 let bds = EcPV.PVMap.add pv (x, fp.f_ty) bds in
                 map := Mid.add m bds !map; x
             | Some (x, _) -> x

           in e_local idx fp.f_ty

      | Fglob     _
      | FhoareF   _ | FhoareS   _
      | FeHoareF _  | FeHoareS _
      | FbdHoareF _ | FbdHoareS _
      | FequivF   _ | FequivS   _
      | FeagerF   _ | Fpr       _ -> raise CannotTranslate

    and auxkd (kd : quantif) : equantif =
      match kd with
      | Lforall -> `EForall
      | Lexists -> `EExists
      | Llambda -> `ELambda

    and auxbd ((x, bd) : binding) =
      match bd with
      | GTty ty -> (x, ty)
      | _ -> raise CannotTranslate

    in fun f -> let e = aux f in (e, !map)

  let xhyps evs =
    let mtypes = Mid.of_list [evs.es_ml; evs.es_mr] in

    fun m (fp: ss_inv): (_ * form) ->
      let fp: form =
        Mid.fold (fun mh pvs fp ->
          let mty = Mid.find_opt mh mtypes in
          let fp  =
            EcPV.Mnpv.fold (fun pv (x, ty) fp ->
              (f_let1 x) (f_pvar pv ty mh).inv fp)
            (EcPV.PVMap.raw pvs) fp
          in f_forall_mems [mh, oget mty] fp)
        m fp.inv
      and cnt =
        Mid.fold
          (fun _ pvs i -> i + 1 + EcPV.Mnpv.cardinal (EcPV.PVMap.raw pvs))
          m 0
      in (cnt, fp)
end

(* -------------------------------------------------------------------- *)
let t_equiv_ll_while_disj_r side inv tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let s, m_side, m_other =
    match side with
    | `Left  -> es.es_sl, es.es_ml, es.es_mr
    | `Right -> es.es_sr, es.es_mr, es.es_ml in
  let (e, c), s = tc1_last_while tc s in
  let ss_inv_generalize_as_side = sideif side EcSubst.ss_inv_generalize_as_left EcSubst.ss_inv_generalize_as_right in
  let e = ss_inv_generalize_as_side (ss_inv_of_expr (EcMemory.memory m_side) e) (fst es.es_ml) (fst es.es_mr) in

  let (_,ll) =
    try
      let evs = tc1_as_equivS tc in
      let ml = EcMemory.memory m_side in
      let m = EcIdent.create "&hr" in
      let rebind_side = sideif side EcSubst.ts_inv_rebind_left EcSubst.ts_inv_rebind_right in
      let inv = rebind_side inv m in
      let e, mexpr = LossLess.form_of_expr env (EcMemory.memory m_other) ml e.inv in
      let c = s_while (e, c) in
      let ts_inv_lower_side1 = sideif side ts_inv_lower_left1 ts_inv_lower_right1 in
      LossLess.xhyps evs mexpr (ts_inv_lower_side1 (fun pre -> f_bdHoareS (snd m_side) pre c {m;inv=f_true} FHeq {m;inv=f_r1}) inv)
    with LossLess.CannotTranslate ->
        tc_error !!tc
          "while linking predicates cannot be converted to expressions"
  in

  (* 1. The body preserves the invariant and the loop is lossless. *)

  let m_other' = (EcIdent.create "&m", EcMemory.memtype m_other) in
  let m = EcIdent.create "&hr" in

  let srebind f = sideif side (EcSubst.ts_inv_rebind f m (fst m_other')) (EcSubst.ts_inv_rebind f (fst m_other') m) in

  let b_pre   = map_ts_inv2 f_and_simpl inv e in
  let b_pre   = srebind b_pre in
  let b_post  = inv in
  let b_post  = srebind b_post in
  let ts_inv_lower_side2 = sideif side ts_inv_lower_left2 ts_inv_lower_right2 in
  let b_concl = ts_inv_lower_side2 (fun pr po ->
    f_bdHoareS (snd m_side) pr c po FHeq {m;inv=f_r1}
  ) b_pre b_post in
  let b_concl = b_concl in
  let b_concl = EcSubst.f_forall_mems_ss_inv m_other' b_concl in

  (* 2. WP of the while *)
  let f_imps_simpl' = map_ts_inv3 (fun f1 f2 f3 -> f_imps_simpl [f1; f2] f3) in
  let post = f_imps_simpl' (map_ts_inv1 f_not_simpl e) inv (es_po es) in
  let modi = s_write env c in
  let generalize_mod_side = sideif side generalize_mod_left generalize_mod_right in
  let post = generalize_mod_side env modi post in
  let post = map_ts_inv2 f_and_simpl inv post in
  let concl =
    let sl, sr = sideif side (s, es.es_sr) (es.es_sl, s) in
    f_equivS (snd es.es_ml) (snd es.es_mr) (es_pr es) sl sr post 
  in

  FApi.xmutate1 tc `While [b_concl; ll; concl]

(* -------------------------------------------------------------------- *)

let t_equiv_while_r inv tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let (el, cl), sl = tc1_last_while tc es.es_sl in
  let (er, cr), sr = tc1_last_while tc es.es_sr in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  let el = ss_inv_generalize_right (ss_inv_of_expr ml el) mr in
  let er = ss_inv_generalize_left (ss_inv_of_expr mr er) ml in
  let sync_cond = map_ts_inv2 f_iff_simpl el er in

  (* 1. The body preserves the invariant *)
  let f_ands_simpl' f = f_ands_simpl (List.tl f) (List.hd f) in
  let b_pre  = map_ts_inv f_ands_simpl' [er; inv; el] in
  let b_post = map_ts_inv2 f_and_simpl inv sync_cond in
  let b_concl = f_equivS (snd es.es_ml) (snd es.es_mr) b_pre cl cr b_post in

  (* 2. WP of the while *)
  let f_imps_simpl' f = f_imps_simpl (List.tl f) (List.hd f) in
  let post = map_ts_inv f_imps_simpl' [es_po es; 
    map_ts_inv1 f_not_simpl el; map_ts_inv1 f_not_simpl er; inv]  in
  let modil = s_write env cl in
  let modir = s_write env cr in
  let post = generalize_mod_ts_inv env modil modir post in
  let post = map_ts_inv2 f_and_simpl b_post post in
  let concl = f_equivS (snd es.es_ml) (snd es.es_mr) (es_pr es) sl sr post in

  FApi.xmutate1 tc `While [b_concl; concl]

(* -------------------------------------------------------------------- *)
let t_hoare_while           = FApi.t_low1 "hoare-while"   t_hoare_while_r
let t_bdhoare_while         = FApi.t_low2 "bdhoare-while" t_bdhoare_while_r
let t_bdhoare_while_rev_geq = FApi.t_low4 "bdhoare-while" t_bdhoare_while_rev_geq_r
let t_bdhoare_while_rev     = FApi.t_low1 "bdhoare-while" t_bdhoare_while_rev_r
let t_equiv_while           = FApi.t_low1 "equiv-while"   t_equiv_while_r
let t_equiv_while_disj      = FApi.t_low3 "equiv-while"   t_equiv_while_disj_r
let t_equiv_ll_while_disj   = FApi.t_low2 "equiv-while"   t_equiv_ll_while_disj_r

(* -------------------------------------------------------------------- *)
let process_while side winfos tc =
  let { EP.wh_inv  = phi ;
        EP.wh_vrnt = vrnt;
        EP.wh_bds  = bds ; } = winfos in

  match (FApi.tc1_goal tc).f_node with
  | FhoareS _ -> begin
      match vrnt with
      | None ->
        t_hoare_while
          (snd (TTC.tc1_process_Xhl_formula tc phi))
          tc
      | _    -> tc_error !!tc "invalid arguments"
    end

  | FeHoareS _ ->
      let _, inv = TTC.tc1_process_Xhl_formula_xreal tc phi in
      t_ehoare_while inv tc

  | FbdHoareS _ -> begin
      match vrnt, bds with
      | Some vrnt, None ->
          let _, phi = TTC.tc1_process_Xhl_formula tc phi in
          let _, vrnt = TTC.tc1_process_Xhl_form tc tint vrnt in
          t_bdhoare_while phi vrnt tc

      | Some vrnt, Some (`Bd (k, eps)) ->
        let _, phi = TTC.tc1_process_Xhl_formula tc phi in
        let _, vrnt = TTC.tc1_process_Xhl_form tc tint vrnt in
        let _, k = TTC.tc1_process_Xhl_form tc tint k in
        let _, eps = TTC.tc1_process_Xhl_form tc treal eps in

        t_bdhoare_while_rev_geq phi vrnt k eps tc
      | None, None ->
          let _, phi = TTC.tc1_process_Xhl_formula tc phi in
          t_bdhoare_while_rev phi tc

      | None, Some _ ->
        tc_error !!tc "invalid arguments"
  end

  | FequivS _ -> begin
      match side, vrnt with
      | None, None ->
          t_equiv_while (TTC.tc1_process_prhl_formula tc phi) tc

      | Some side, Some vrnt ->
          t_equiv_while_disj side
            (TTC.tc1_process_prhl_form    tc tint vrnt)
            (TTC.tc1_process_prhl_formula tc phi)
            tc

      | Some side, None ->
        t_equiv_ll_while_disj side
            (TTC.tc1_process_prhl_formula tc phi)
            tc

      | _ -> tc_error !!tc "invalid arguments"
  end

  | _ -> tc_error !!tc "expecting a hoare[...]/equiv[...]"

(* -------------------------------------------------------------------- *)
let process_async_while (winfos : EP.async_while_info) tc =
  let e_and e1 e2 =
    let p = EcCoreLib.CI_Bool.p_and in
    e_app (e_op p [] (toarrow [tbool; tbool] tbool)) [e1; e2] tbool
  in

  let { EP.asw_inv  = inv     ;
        EP.asw_test = ((t1,f1), (t2,f2));
        EP.asw_pred = (p0, p1); } = winfos in

  let evs  = tc1_as_equivS tc in
  let env  = FApi.tc1_env  tc in
  let hyps = FApi.tc1_hyps tc in

  let ml = EcMemory.memory evs.es_ml in
  let mr = EcMemory.memory evs.es_mr in

  let (el, cl), sl = tc1_last_while tc evs.es_sl in
  let (er, cr), sr = tc1_last_while tc evs.es_sr in

  let inv = TTC.tc1_process_prhl_formula tc inv in
  let p0  = TTC.tc1_process_prhl_formula tc  p0 in
  let p1  = TTC.tc1_process_prhl_formula tc  p1 in
  let f1  = TTC.tc1_process_prhl_form_opt tc None f1 in
  let f2  = TTC.tc1_process_prhl_form_opt tc None f2 in
  let t1  = TTC.tc1_process_Xhl_exp tc (Some `Left ) (Some (tfun f1.inv.f_ty tbool)) t1 in
  let t2  = TTC.tc1_process_Xhl_exp tc (Some `Right) (Some (tfun f2.inv.f_ty tbool)) t2 in
  let ft1 = ss_inv_generalize_right (ss_inv_of_expr ml t1) mr in
  let ft2 = ss_inv_generalize_left (ss_inv_of_expr mr t2) ml in
  let fe1 = ss_inv_generalize_right (ss_inv_of_expr ml el) mr in
  let fe2 = ss_inv_generalize_left (ss_inv_of_expr mr er) ml in
  let fe  = map_ts_inv2 f_or fe1 fe2 in
  let f_app' f = f_app (List.hd f) (List.tl f) tbool in
  let f_imps' f = f_imps (List.tl f) (List.hd f) in
  let cond1 = EcSubst.f_forall_mems_ts_inv evs.es_ml evs.es_mr
    (map_ts_inv f_imps' [map_ts_inv f_ands [fe1; fe2;
    map_ts_inv f_app' [ft1; f1];
    map_ts_inv f_app' [ft2; f2]]; 
    inv; fe; p0]) in

  let cond2 = EcSubst.f_forall_mems_ts_inv evs.es_ml evs.es_mr
    (map_ts_inv f_imps' [fe1; inv; fe; map_ts_inv1 f_not p0; p1]) in

  let cond3 = EcSubst.f_forall_mems_ts_inv evs.es_ml evs.es_mr
    (map_ts_inv f_imps' [fe2; inv; fe; map_ts_inv1 f_not p0; map_ts_inv1 f_not p1]) in

  let xwh =
    let v1, v2 = as_seq2 (EcEnv.LDecl.fresh_ids hyps ["v1_"; "v2_"]) in
    let fv1 = {ml;mr;inv=f_local v1 f1.inv.f_ty} in
    let fv2 = {ml;mr;inv=f_local v2 f2.inv.f_ty} in
    let ev1 = e_local v1 f1.inv.f_ty in
    let ev2 = e_local v2 f2.inv.f_ty in
    let eq1 = map_ts_inv2 f_eq fv1 f1 and eq2 = map_ts_inv2 f_eq fv2 f2 in
    let pr = map_ts_inv f_ands [inv; fe; p0; eq1; eq2] in
    let po = inv in
    let wl = s_while (e_and el (e_app t1 [ev1] tbool), cl) in
    let wr = s_while (e_and er (e_app t2 [ev2] tbool), cr) in
    EcFol.f_forall [(v1, GTty f1.inv.f_ty); (v2, GTty f2.inv.f_ty)]
      (f_equivS (snd evs.es_ml) (snd evs.es_mr) pr wl wr po)
  in

  let hr1, hr2 =
    let hr1 =
      let el = ss_inv_generalize_right (ss_inv_of_expr ml el) mr in
      let pre = map_ts_inv f_ands [inv; el ; map_ts_inv1 f_not p0; p1] in
      EcSubst.f_forall_mems_ss_inv evs.es_mr
        (ts_inv_lower_left2 (fun pr po -> f_hoareS (snd evs.es_ml) pr cl po) pre inv)

    and hr2 =
      let er = ss_inv_generalize_left (ss_inv_of_expr mr er) ml in
      let pre = map_ts_inv f_ands [inv; er; map_ts_inv1 f_not p0; map_ts_inv1 f_not p1] in
      EcSubst.f_forall_mems_ss_inv evs.es_ml
        (ts_inv_lower_right2 (fun pr po -> f_hoareS (snd evs.es_mr) pr cr po) pre inv)

    in (hr1, hr2)
  in


  let (c1, ll1), (c2, ll2) =
    try
      let ll1 =
        let test    = f_ands [fe1.inv; f_not p0.inv; p1.inv] in
        let test, m = LossLess.form_of_expr env (EcMemory.memory evs.es_mr) ml test in
        let c       = s_while (test, cl) in
        LossLess.xhyps evs m
          (ts_inv_lower_left3 (fun inv f_tr f_r1 -> f_bdHoareS (snd evs.es_ml) inv c f_tr FHeq f_r1) inv {ml;mr;inv=f_true} {ml;mr;inv=f_r1})

      and ll2 =
        let test    = f_ands [fe1.inv; f_not p0.inv; f_not p1.inv] in
        let test, m = LossLess.form_of_expr env (EcMemory.memory evs.es_ml) mr test in
        let c       = s_while (test, cr) in
        LossLess.xhyps evs m
          (ts_inv_lower_right3  (fun inv f_tr f_r1 -> f_bdHoareS (snd evs.es_mr) inv c f_tr FHeq f_r1) inv {ml;mr;inv=f_true} {ml;mr;inv=f_r1})

      in (ll1, ll2)

    with LossLess.CannotTranslate ->
      tc_error !!tc
        "async-while linking predicates cannot be converted to expressions"
  in

  let concl =
    let f_imps' f = f_imps (List.tl f) (List.hd f) in
    let post  = map_ts_inv f_imps' [es_po evs; map_ts_inv1 f_not fe1; map_ts_inv1 f_not fe2; inv] in
    let modil = s_write env cl in
    let modir = s_write env cr in
    let post  = generalize_mod_ts_inv env modil modir post in
    f_equivS (snd evs.es_ml) (snd evs.es_mr) (es_pr evs) sl sr (map_ts_inv2 f_and inv post) in

  FApi.t_onfsub (function
    | 6 -> Some (EcLowGoal.t_intros_n c1)
    | 7 -> Some (EcLowGoal.t_intros_n c2)
    | _ -> None)

    (FApi.xmutate1
       tc `AsyncWhile
         [cond1; cond2; cond3; hr1; hr2; xwh; ll1; ll2; concl])
