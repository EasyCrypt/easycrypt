(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcParsetree
open EcTypes
open EcFol
open EcAst
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let t_hoare_seq_r i phi tc =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_hoareS tc in
  let phi = ss_inv_rebind phi (fst hs.hs_m) in
  let s1, s2 = s_split env i hs.hs_s in
  let a = f_hoareS (snd hs.hs_m) (hs_pr hs) (stmt s1) phi in
  let b = f_hoareS (snd hs.hs_m) phi (stmt s2) (hs_po hs) in
  FApi.xmutate1 tc `HlApp [a; b]

let t_hoare_seq = FApi.t_low2 "hoare-seq" t_hoare_seq_r

(* -------------------------------------------------------------------- *)
let t_ehoare_seq_r i phi tc =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_ehoareS tc in
  let s1, s2 = s_split env i hs.ehs_s in
  let phi = ss_inv_rebind phi (fst hs.ehs_m) in
  let a = f_eHoareS (snd hs.ehs_m) (ehs_pr hs) (stmt s1) phi in
  let b = f_eHoareS (snd hs.ehs_m) phi (stmt s2) (ehs_po hs) in
  FApi.xmutate1 tc `HlApp [a; b]

let t_ehoare_seq = FApi.t_low2 "hoare-seq" t_ehoare_seq_r

(* -------------------------------------------------------------------- *)
let t_bdhoare_seq_r_low i (phi, pR, f1, f2, g1, g2) tc =
  let env = FApi.tc1_env tc in
  let bhs = tc1_as_bdhoareS tc in
  let m = fst bhs.bhs_m in
  let phi = ss_inv_rebind phi m in
  let pR = ss_inv_rebind pR m in
  let f1 = ss_inv_rebind f1 m in
  let f2 = ss_inv_rebind f2 m in
  let g1 = ss_inv_rebind g1 m in
  let g2 = ss_inv_rebind g2 m in
  let s1, s2 = s_split env i bhs.bhs_s in
  let s1, s2 = stmt s1, stmt s2 in
  let nR = map_ss_inv1 f_not pR in
  let mt = snd bhs.bhs_m in
  let cond_phi = f_hoareS mt (bhs_pr bhs) s1 phi in
  let condf1 = f_bdHoareS mt (bhs_pr bhs) s1 pR bhs.bhs_cmp f1 in
  let condg1 = f_bdHoareS mt (bhs_pr bhs) s1 nR bhs.bhs_cmp g1 in
  let condf2 = f_bdHoareS mt (map_ss_inv2 f_and_simpl phi pR) s2 (bhs_po bhs) bhs.bhs_cmp f2 in
  let condg2 = f_bdHoareS mt (map_ss_inv2 f_and_simpl phi nR) s2 (bhs_po bhs) bhs.bhs_cmp g2 in
  let bd =
    (map_ss_inv2 f_real_add_simpl (map_ss_inv2 f_real_mul_simpl f1 f2) (map_ss_inv2 f_real_mul_simpl g1 g2)) in
  let condbd =
    match bhs.bhs_cmp with
    | FHle -> map_ss_inv2 f_real_le bd (bhs_bd bhs)
    | FHeq -> map_ss_inv2 f_eq bd (bhs_bd bhs)
    | FHge -> map_ss_inv2 f_real_le (bhs_bd bhs) bd in
  let condbd = map_ss_inv2 f_imp (bhs_pr bhs) condbd in
  let (ir1, ir2) = EcIdent.create "r", EcIdent.create "r" in
  let (r1 , r2 ) = f_local ir1 treal, f_local ir2 treal in
  let condnm =
    let eqs = map_ss_inv2 f_and (map_ss_inv1 ((EcUtils.flip f_eq) r1) f2)
                                (map_ss_inv1 ((EcUtils.flip f_eq) r2) g2) in
    f_forall
      [(ir1, GTty treal); (ir2, GTty treal)]
      (f_hoareS (snd bhs.bhs_m) (map_ss_inv2 f_and (bhs_pr bhs) eqs) s1 eqs) in
  let conds = [EcSubst.f_forall_mems_ss_inv bhs.bhs_m condbd; condnm] in
  let conds =
    if   f_equal g1.inv f_r0
    then condg1 :: conds
    else if   f_equal g2.inv f_r0
         then condg2 :: conds
         else condg1 :: condg2 :: conds in

  let conds =
    if   f_equal f1.inv f_r0
    then condf1 :: conds
    else if   f_equal f2.inv f_r0
         then condf2 :: conds
         else condf1 :: condf2 :: conds in

  let conds = cond_phi :: conds in

  FApi.xmutate1 tc `HlApp conds

(* -------------------------------------------------------------------- *)
let t_bdhoare_seq_r i info tc =
  let tactic tc =
    let hs  = tc1_as_hoareS tc in
    let tt1 = EcPhlConseq.t_hoareS_conseq_nm (hs_pr hs) {m=(fst hs.hs_m);inv=f_true} in
    let tt2 = EcPhlAuto.t_pl_trivial in
    FApi.t_seqs [tt1; tt2; t_fail] tc
  in

  FApi.t_last
    (FApi.t_try (t_intros_s_seq (`Symbol ["_"; "_"]) tactic))
    (t_bdhoare_seq_r_low i info tc)

let t_bdhoare_seq = FApi.t_low2 "bdhoare-seq" t_bdhoare_seq_r

(* -------------------------------------------------------------------- *)
let t_equiv_seq (i, j) phi tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let sl1,sl2 = s_split env i es.es_sl in
  let sr1,sr2 = s_split env j es.es_sr in
  let mtl, mtr = snd es.es_ml, snd es.es_mr in
  let a = f_equivS mtl mtr (es_pr es) (stmt sl1) (stmt sr1) phi in
  let b = f_equivS mtl mtr phi (stmt sl2) (stmt sr2) (es_po es) in

  FApi.xmutate1 tc `HlApp [a; b]

let t_equiv_seq_onesided side i pre post tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let (ml, mr) = fst es.es_ml, fst es.es_mr in
  let s, s', p', q' =
    match side with
    | `Left  -> 
      let p' = ss_inv_generalize_as_left pre ml mr in
      let q' = ss_inv_generalize_as_left post ml mr in
      es.es_sl, es.es_sr, p', q'
    | `Right -> 
      let p' = ss_inv_generalize_as_right pre ml mr in
      let q' = ss_inv_generalize_as_right post ml mr in
      es.es_sr, es.es_sl, p', q'
  in
  let generalize_mod_side= sideif side generalize_mod_left generalize_mod_right in
  let ij =
    match side with
    | `Left  -> (i, Zpr.cpos (List.length s'. s_node))
    | `Right -> (Zpr.cpos (List.length s'. s_node), i) in
  let _s1, s2 = s_split env i s in

  let modi = EcPV.s_write env (EcModules.stmt s2) in
  let r = map_ts_inv2 f_and p' (generalize_mod_side env modi (map_ts_inv2 f_imp q' (es_po es))) in
  FApi.t_seqsub (t_equiv_seq ij r)
    [t_id; (* s1 ~ s' : pr ==> r *)
     FApi.t_seqsub (EcPhlConseq.t_equivS_conseq_nm p' q')
       [(* r => forall mod, post => post' *) t_trivial;
        (* r => p' *) t_trivial;
        (* s1 ~ [] : p' ==> q' *) EcPhlConseq.t_equivS_conseq_bd side pre post
       ]
    ] tc

(* -------------------------------------------------------------------- *)
let process_phl_bd_info bd_info tc =
  match bd_info with
  | PSeqNone ->
      let hs = tc1_as_bdhoareS tc in
      let m = fst hs.bhs_m in
      let f1, f2 = bhs_bd hs, {m;inv=f_r1} in
        (* The last argument will not be used *)
        ({m;inv=f_true}, f1, f2, {m;inv=f_r0}, {m;inv=f_r1})

  | PSeqSingle f ->
      let hs = tc1_as_bdhoareS tc in
      let m = fst hs.bhs_m in
      let f  = snd (TTC.tc1_process_Xhl_form tc treal f) in
      let f1, f2 = (map_ss_inv2 f_real_div (bhs_bd hs) f, f) in
        ({m;inv=f_true}, f1, f2, {m;inv=f_r0}, {m;inv=f_r1})

  | PSeqMult (phi, f1, f2, g1, g2) ->
    let hs = tc1_as_bdhoareS tc in
    let m = fst hs.bhs_m in
      let phi =
        phi |> omap (fun f -> snd (TTC.tc1_process_Xhl_formula tc f))
            |> odfl {m;inv=f_true} in

      let check_0 f =
        if not (f_equal f f_r0) then
          tc_error !!tc "the formula must be 0%%r" in

      let process_f (f1,f2) =
        match f1, f2 with
        | None, None -> assert false

        | Some fp, None ->
            let _, f = TTC.tc1_process_Xhl_form tc treal fp in
            reloc fp.pl_loc check_0 f.inv; (f, {m;inv=f_r1})

        | None, Some fp ->
            let _, f = TTC.tc1_process_Xhl_form tc treal fp in
            reloc fp.pl_loc check_0 f.inv; ({m;inv=f_r1}, f)

        | Some f1, Some f2 ->
            let _, f1 = TTC.tc1_process_Xhl_form tc treal f1 in
            let _, f2 = TTC.tc1_process_Xhl_form tc treal f2 in
            (f1, f2)
      in

      let f1, f2 = process_f (f1, f2) in
      let g1, g2 = process_f (g1, g2) in

      (phi, f1, f2, g1, g2)

(* -------------------------------------------------------------------- *)
let process_seq ((side, k, phi, bd_info) : seq_info) (tc : tcenv1) =
  let concl = FApi.tc1_goal tc in

  let get_single phi =
    match phi with
    | Single phi -> phi
    | Double _   -> tc_error !!tc "seq: a single formula is expected" in

  let check_side side =
    if EcUtils.is_some side then
      tc_error !!tc "seq: no side information expected" in

  match k, bd_info with
  | Single i, PSeqNone when is_hoareS concl ->
    check_side side;
    let _, phi = TTC.tc1_process_Xhl_formula tc (get_single phi) in
    let i = EcLowPhlGoal.tc1_process_codepos1 tc (side, i) in
    t_hoare_seq i phi tc

  | Single i, PSeqNone when is_eHoareS concl ->
    check_side side;
    let _, phi = TTC.tc1_process_Xhl_formula_xreal tc (get_single phi) in
    let i = EcLowPhlGoal.tc1_process_codepos1 tc (side, i) in
    t_ehoare_seq i phi tc

  | Single i, PSeqNone when is_equivS concl ->
    let pre, post =
      match phi with
      | Single _ -> tc_error !!tc "seq onsided: a pre and a post is expected"
      | Double (pre, post) ->
        let _, pre  = TTC.tc1_process_Xhl_formula ?side tc pre in
        let _, post = TTC.tc1_process_Xhl_formula ?side tc post in
        (pre, post) in
    let side =
      match side with
      | None -> tc_error !!tc "seq onsided: side information expected"
      | Some side -> side in
    let i = EcLowPhlGoal.tc1_process_codepos1 tc (Some side, i) in
    t_equiv_seq_onesided side i pre post tc

  | Single i, _ when is_bdHoareS concl ->
      check_side side;
      let _, pia = TTC.tc1_process_Xhl_formula tc (get_single phi) in
      let (ra, f1, f2, f3, f4) = process_phl_bd_info bd_info tc in
      let i = EcLowPhlGoal.tc1_process_codepos1 tc (side, i) in
      t_bdhoare_seq i (ra, pia, f1, f2, f3, f4) tc

  | Double (i, j), PSeqNone when is_equivS concl ->
      check_side side;
      let phi = TTC.tc1_process_prhl_formula tc (get_single phi) in
      let i = EcLowPhlGoal.tc1_process_codepos1 tc (Some `Left, i) in
      let j = EcLowPhlGoal.tc1_process_codepos1 tc (Some `Left, j) in
      t_equiv_seq (i, j) phi tc

  | Single _, PSeqNone
  | Double _, PSeqNone ->
      tc_error !!tc "invalid `position' parameter"

  | _, _ ->
      tc_error !!tc "optional bound parameter not supported"
