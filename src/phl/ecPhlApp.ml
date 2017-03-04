(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcParsetree
open EcTypes
open EcModules
open EcFol

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let t_hoare_app_r i phi tc =
  let hs = tc1_as_hoareS tc in
  let s1, s2 = s_split i hs.hs_s in
  let a = f_hoareS_r { hs with hs_s = stmt s1; hs_po = phi }  in
  let b = f_hoareS_r { hs with hs_pr = phi; hs_s = stmt s2 } in
  FApi.xmutate1 tc `HlApp [a; b]

let t_hoare_app = FApi.t_low2 "hoare-app" t_hoare_app_r

(* -------------------------------------------------------------------- *)
let t_ahoare_app_r i (dir, b1) phi tc =
  let ahs = tc1_as_ahoareS tc in
  let s1, s2 = s_split i ahs.ahs_s in

  let b2 = f_real_sub_simpl ahs.ahs_b b1 in

  let (b1, b2) =
    match dir with
    | Backs -> (b1, b2)
    | Fwds  -> (b2, b1)
  in

  let g1 = f_ahoareS_r
    { ahs with ahs_b = b2; ahs_s = stmt s1; ahs_po = phi }  in
  let g2 = f_ahoareS_r
    { ahs with ahs_b = b1; ahs_pr = phi; ahs_s = stmt s2 } in

  FApi.xmutate1 tc `AHlApp [g1; g2]

let t_ahoare_app = FApi.t_low3 "hoare-app" t_ahoare_app_r

(* -------------------------------------------------------------------- *)
let t_bdhoare_app_r_low i (phi, pR, f1, f2, g1, g2) tc =
  let bhs = tc1_as_bdhoareS tc in
  let s1, s2 = s_split i bhs.bhs_s in
  let s1, s2 = stmt s1, stmt s2 in
  let nR = f_not pR in
  let cond_phi = f_hoareS bhs.bhs_m bhs.bhs_pr s1 phi in
  let condf1 = f_bdHoareS_r { bhs with bhs_s = s1; bhs_po = pR; bhs_bd = f1; } in
  let condg1 = f_bdHoareS_r { bhs with bhs_s = s1; bhs_po = nR; bhs_bd = g1; } in
  let condf2 = f_bdHoareS_r
    { bhs with bhs_s = s2; bhs_pr = f_and_simpl phi pR; bhs_bd = f2; } in
  let condg2 = f_bdHoareS_r
    { bhs with bhs_s = s2; bhs_pr = f_and_simpl phi nR; bhs_bd = g2; } in
  let bd =
    (f_real_add_simpl (f_real_mul_simpl f1 f2) (f_real_mul_simpl g1 g2)) in
  let condbd =
    match bhs.bhs_cmp with
    | FHle -> f_real_le bd bhs.bhs_bd
    | FHeq -> f_eq bd bhs.bhs_bd
    | FHge -> f_real_le bhs.bhs_bd bd in
  let condbd = f_imp bhs.bhs_pr condbd in
  let (ir1, ir2) = EcIdent.create "r", EcIdent.create "r" in
  let (r1 , r2 ) = f_local ir1 treal, f_local ir2 treal in
  let condnm =
    let eqs = f_and (f_eq f2 r1) (f_eq g2 r2) in
    f_forall
      [(ir1, GTty treal); (ir2, GTty treal)]
      (f_hoareS bhs.bhs_m (f_and bhs.bhs_pr eqs) s1 eqs) in
  let conds = [f_forall_mems [bhs.bhs_m] condbd; condnm] in
  let conds =
    if   f_equal g1 f_r0
    then condg1 :: conds
    else if   f_equal g2 f_r0
         then condg2 :: conds
         else condg1 :: condg2 :: conds in

  let conds =
    if   f_equal f1 f_r0
    then condf1 :: conds
    else if   f_equal f2 f_r0
         then condf2 :: conds
         else condf1 :: condf2 :: conds in

  let conds = cond_phi :: conds in

  FApi.xmutate1 tc `HlApp conds

(* -------------------------------------------------------------------- *)
let t_bdhoare_app_r i info tc =
  let tactic tc =
    let hs  = tc1_as_hoareS tc in
    let tt1 = EcPhlConseq.t_hoareS_conseq_nm hs.hs_pr f_true in
    let tt2 = EcHiGoal.process_trivial in
    FApi.t_seqs [tt1; tt2; t_fail] tc
  in

  FApi.t_last
    (FApi.t_try (t_intros_s_seq (`Symbol ["_"; "_"]) tactic))
    (t_bdhoare_app_r_low i info tc)

let t_bdhoare_app = FApi.t_low2 "bdhoare-app" t_bdhoare_app_r

(* -------------------------------------------------------------------- *)
let t_equiv_app (i, j) phi tc =
  let es = tc1_as_equivS tc in
  let sl1,sl2 = s_split i es.es_sl in
  let sr1,sr2 = s_split j es.es_sr in
  let a = f_equivS_r {es with es_sl=stmt sl1; es_sr=stmt sr1; es_po=phi} in
  let b = f_equivS_r {es with es_pr=phi; es_sl=stmt sl2; es_sr=stmt sr2} in

  FApi.xmutate1 tc `HlApp [a; b]

let t_equiv_app_onesided side i pre post tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let m, s, s' =
    match side with
    | `Left  -> es.es_ml, es.es_sl, es.es_sr
    | `Right -> es.es_mr, es.es_sr, es.es_sl
  in
  let ij =
    match side with
    | `Left  -> (i, List.length s'. s_node)
    | `Right -> (List.length s'. s_node, i) in
  let _s1, s2 = s_split i s in

  let modi = EcPV.s_write env (EcModules.stmt s2) in
  let subst = Fsubst.f_subst_mem mhr (fst m) in
  let p' = subst pre and q' = subst post in
  let r = f_and p' (generalize_mod env (fst m) modi (f_imp q' es.es_po)) in
  FApi.t_seqsub (t_equiv_app ij r)
    [t_id; (* s1 ~ s' : pr ==> r *)
     FApi.t_seqsub (EcPhlConseq.t_equivS_conseq_nm p' q')
       [(* r => forall mod, post => post' *) t_logic_trivial;
        (* r => p' *) t_logic_trivial;
        (* s1 ~ [] : p' ==> q' *) EcPhlConseq.t_equivS_conseq_bd side pre post
       ]
    ] tc

(* -------------------------------------------------------------------- *)
let t_aequiv_app (i, j) (dir, (dp, ep)) phi tc =
  let aes = tc1_as_aequivS tc in
  let sl1,sl2 = s_split i aes.aes_sl in
  let sr1,sr2 = s_split j aes.aes_sr in

  let dp' = f_real_sub_simpl aes.aes_dp dp in
  let ep' = f_real_sub_simpl aes.aes_ep ep in

  let ((dpa, epa), (dpb, epb)) =
    match dir with
    | Backs -> ((dp , ep ), (dp', ep'))
    | Fwds  -> ((dp', ep'), (ep , dp ))
  in

  let a = f_aequivS_r { aes with aes_dp = dpa; aes_ep = epa;
    aes_sl=stmt sl1; aes_sr=stmt sr1; aes_po=phi; } in

  let b = f_aequivS_r { aes with aes_dp = dpb; aes_ep = epb;
    aes_pr=phi; aes_sl=stmt sl2; aes_sr=stmt sr2; } in

  FApi.xmutate1 tc `HlApp [a; b]

(* -------------------------------------------------------------------- *)
let process_phl_bd_info dir bd_info tc =
  match bd_info with
  | None ->
      let hs = tc1_as_bdhoareS tc in
      let f1, f2 =
         match dir with
        | Backs -> hs.bhs_bd, f_r1
        | Fwds  -> f_r1, hs.bhs_bd
      in
        (* The last argument will not be used *)
        (f_true, f1, f2, f_r0, f_r1)

  | Some (PAppSingle f) ->
      let hs = tc1_as_bdhoareS tc in
      let f  = TTC.tc1_process_Xhl_form tc treal f in
      let f1, f2 =
        match dir with
        | Backs  -> (f_real_div hs.bhs_bd f, f)
        | Fwds   -> (f, f_real_div hs.bhs_bd f)
      in
        (f_true, f1, f2, f_r0, f_r1)

  | Some (PAppMult (phi, f1, f2, g1, g2)) ->
      let phi =
        phi |> omap (TTC.tc1_process_Xhl_formula tc)
            |> odfl f_true in

      let check_0 f =
        if not (f_equal f f_r0) then
          tc_error !!tc "the formula must be 0%%r" in

      let process_f (f1,f2) =
        match f1, f2 with
        | None, None -> assert false

        | Some fp, None ->
            let f = TTC.tc1_process_Xhl_form tc treal fp in
            reloc fp.pl_loc check_0 f; (f, f_r1)

        | None, Some fp ->
            let f = TTC.tc1_process_Xhl_form tc treal fp in
            reloc fp.pl_loc check_0 f; (f_r1, f)

        | Some f1, Some f2 ->
            (TTC.tc1_process_Xhl_form tc treal f1,
             TTC.tc1_process_Xhl_form tc treal f2)
      in

      let f1, f2 = process_f (f1, f2) in
      let g1, g2 = process_f (g1, g2) in

      (phi, f1, f2, g1, g2)

(* -------------------------------------------------------------------- *)
let process_phl_ae_info dir ae_info tc =
  match ae_info with
  | None ->
     (dir, (f_r0, f_r0))

  | Some (ep, dp) ->
     let dp = TTC.tc1_process_form tc treal dp in
     let ep = TTC.tc1_process_form tc treal ep in
     (dir, (dp, ep))

(* -------------------------------------------------------------------- *)
let process_phl_ac_info dir b tc =
  let b = b |> omap (TTC.tc1_process_form tc treal) |> odfl f_r0 in
  (dir, b)

(* -------------------------------------------------------------------- *)
let process_app (side, dir, k, phi, seq_info) tc =
  let concl = FApi.tc1_goal tc in

  let is_bd_info = function None | Some (PAppBd   _) -> true | _ -> false in
  let is_ae_info = function None | Some (PAppDiff _) -> true | _ -> false in
  let is_ac_info = function None | Some (PAppAcc  _) -> true | _ -> false in

  let as_bd_info =
    function
    | None -> Some None
    | Some (PAppBd bd) -> Some (Some bd)
    | _ -> None

  and as_ae_info =
    function
    | None -> Some None
    | Some (PAppDiff ae) -> Some (Some ae)
    | _  -> None

  and as_ac_info =
    function
    | None -> Some None
    | Some (PAppAcc b) -> Some (Some b)
    | _  -> None
  in

  let get_single phi =
    match phi with
    | Single phi -> phi
    | Double _   -> tc_error !!tc "seq: a single formula is expected" in

  let check_side side =
    if EcUtils.is_some side then
      tc_error !!tc "seq: no side information expected" in

  match k, seq_info with
  | Single i, None when is_hoareS concl ->
    check_side side;
    let phi = TTC.tc1_process_Xhl_formula tc (get_single phi) in
    t_hoare_app i phi tc

  | Single i, None when is_equivS concl ->
    let side =
      match side with
      | None -> tc_error !!tc "seq onsided: side information expected"
      | Some side -> side in
    let pre, post =
      match phi with
      | Single _ -> tc_error !!tc "seq onsided: a pre and a post is expected"
      | Double (pre, post) ->
        TTC.tc1_process_Xhl_formula ~side tc pre,
        TTC.tc1_process_Xhl_formula ~side tc post in
    t_equiv_app_onesided side i pre post tc

  | Double (i, j), None when is_equivS concl ->
      let phi = TTC.tc1_process_prhl_formula tc (get_single phi) in
      t_equiv_app (i, j) phi tc

  | Double (i, j), _ when is_ae_info seq_info && is_aequivS concl ->
     let ae = oget (as_ae_info seq_info) in
     let ae = process_phl_ae_info dir ae tc in
     let phi = TTC.tc1_process_aprhl_formula tc (get_single phi) in
     t_aequiv_app (i, j) ae phi tc

  | Single i, _ when is_ac_info seq_info && is_ahoareS concl ->
     let b   = oget (as_ac_info seq_info) in
     let b   = process_phl_ac_info dir b tc in
     let phi = TTC.tc1_process_Xhl_formula tc (get_single phi) in
     t_ahoare_app i b phi tc

  | Single i, _ when is_bd_info seq_info && is_bdHoareS concl ->
      let bd_info = oget (as_bd_info seq_info) in
      let pia = TTC.tc1_process_Xhl_formula tc (get_single phi) in
      let (ra, f1, f2, f3, f4) = process_phl_bd_info dir bd_info tc in
      t_bdhoare_app i (ra, pia, f1, f2, f3, f4) tc

  | Single _, None
  | Double _, None ->
      tc_error !!tc "invalid `position' parameter"

  | _, _ ->
      tc_error !!tc "optional seq parameter not supported"
