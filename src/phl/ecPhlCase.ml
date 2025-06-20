(* --------------------------------------------------------------------- *)
open EcFol
open EcCoreGoal
open EcLowPhlGoal
open EcAst

(* --------------------------------------------------------------------- *)
let t_hoare_case_r ?(simplify = true) f tc =
  let fand = if simplify then f_and_simpl else f_and in
  let hs = tc1_as_hoareS tc in
  let mt = snd hs.hs_m in
  let concl1 = f_hoareS mt (map_ss_inv2 fand (hs_pr hs) f) hs.hs_s (hs_po hs) in
  let concl2 = f_hoareS mt (map_ss_inv2 fand (hs_pr hs) (map_ss_inv1 f_not f)) hs.hs_s (hs_po hs) in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_ehoare_case_r ?(simplify = true) f tc =
  let _ = simplify in
  let hs = tc1_as_ehoareS tc in
  let mt = snd hs.ehs_m in
  let concl1 = f_eHoareS mt (map_ss_inv2 f_interp_ehoare_form f (ehs_pr hs)) hs.ehs_s (ehs_po hs) in
  let concl2 = f_eHoareS mt (map_ss_inv2 f_interp_ehoare_form (map_ss_inv1 f_not f) (ehs_pr hs)) hs.ehs_s (ehs_po hs) in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_bdhoare_case_r ?(simplify = true) f tc =
  let fand = if simplify then f_and_simpl else f_and in
  let bhs = tc1_as_bdhoareS tc in
  let mt = snd bhs.bhs_m in
  let concl1 = f_bdHoareS mt (map_ss_inv2 fand (bhs_pr bhs) f) bhs.bhs_s (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs) in
  let concl2 = f_bdHoareS mt
    (map_ss_inv2 fand (bhs_pr bhs) (map_ss_inv1 f_not f)) bhs.bhs_s (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs) in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_equiv_case_r ?(simplify = true) f tc =
  let fand = if simplify then f_and_simpl else f_and in
  let es = tc1_as_equivS tc in
  let mtl, mtr = snd es.es_ml, snd es.es_mr in
  let concl1 = f_equivS mtl mtr (map_ts_inv2 fand (es_pr es) f) es.es_sl es.es_sr (es_po es) in
  let concl2 = f_equivS mtl mtr (map_ts_inv2 fand (es_pr es) (map_ts_inv1 f_not f)) es.es_sl es.es_sr (es_po es) in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_hoare_case ?simplify =
  FApi.t_low1 "hoare-case" (t_hoare_case_r ?simplify)

let t_ehoare_case ?simplify =
  FApi.t_low1 "ehoare-case" (t_ehoare_case_r ?simplify)

let t_bdhoare_case ?simplify =
  FApi.t_low1 "bdhoare-case" (t_bdhoare_case_r ?simplify)

let t_equiv_case ?simplify =
  FApi.t_low1 "equiv-case" (t_equiv_case_r ?simplify)

(* --------------------------------------------------------------------- *)
let t_hl_case_r ?simplify f tc =
  match f with
  | Inv_ss f ->
    t_hS_or_bhS_or_eS
      ~th:(t_hoare_case ?simplify f)
      ~teh:(t_ehoare_case ?simplify f)
      ~tbh:(t_bdhoare_case ?simplify f)
      ~te:(fun _ -> tc_error !!tc "expecting a two sided formula")
      tc
  | Inv_ts f ->
    let err _ =
      tc_error !!tc "expecting a one sided formula" in
    t_hS_or_bhS_or_eS
      ~th:err
      ~teh:err
      ~tbh:err
      ~te:(t_equiv_case ?simplify f)
      tc

(* -------------------------------------------------------------------- *)
let t_hl_case ?simplify = FApi.t_low1 "hl-case" (t_hl_case_r ?simplify)
