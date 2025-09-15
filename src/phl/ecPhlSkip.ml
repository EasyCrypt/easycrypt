(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal
open EcLowGoal

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  (* ------------------------------------------------------------------ *)
  let t_hoare_skip_r tc =
    let hs = tc1_as_hoareS tc in

    if not (List.is_empty hs.hs_s.s_node) then
      tc_error !!tc "instruction list is not empty";

    let concl = map_ss_inv2 f_imp (hs_pr hs) (hs_po hs) in
    let concl = EcSubst.f_forall_mems_ss_inv hs.hs_m concl in

    FApi.xmutate1 tc `Skip [concl]

  let t_hoare_skip = FApi.t_low0 "hoare-skip" t_hoare_skip_r

  (* ------------------------------------------------------------------ *)
  let t_ehoare_skip_r tc =
    let hs = tc1_as_ehoareS tc in

    if not (List.is_empty hs.ehs_s.s_node) then
      tc_error !!tc "instruction list is not empty";

    let concl = map_ss_inv2 f_xreal_le (ehs_po hs) (ehs_pr hs) in
    let concl = EcSubst.f_forall_mems_ss_inv hs.ehs_m concl in

    FApi.xmutate1 tc `Skip [concl]

  let t_ehoare_skip = FApi.t_low0 "ehoare-skip" t_ehoare_skip_r

  (* ------------------------------------------------------------------ *)
  let t_bdhoare_skip_r_low tc =
    let bhs = tc1_as_bdhoareS tc in

    if not (List.is_empty bhs.bhs_s.s_node) then
      tc_error !!tc ~who:"skip" "instruction list is not empty";
    if bhs.bhs_cmp <> FHeq && bhs.bhs_cmp <> FHge then
      tc_error !!tc ~who:"skip" "";

    let concl = map_ss_inv2 f_imp (bhs_pr bhs) (bhs_po bhs) in
    let concl = EcSubst.f_forall_mems_ss_inv bhs.bhs_m concl in
    let goals =
      if   f_equal (bhs_bd bhs).inv f_r1
      then [concl]
      else [f_eq (bhs_bd bhs).inv f_r1; concl]
    in

    FApi.xmutate1 tc `Skip goals

  (* ------------------------------------------------------------------ *)
  let t_bdhoare_skip_r tc =
    let t_trivial = FApi.t_seqs [t_simplify ~delta:`No; t_split; t_fail] in
    let bhs = tc1_as_bdhoareS tc in
    let f_r1: EcAst.ss_inv = {m=fst bhs.bhs_m; inv=f_r1} in
    let t_conseq  = EcPhlConseq.t_bdHoareS_conseq_bd FHeq f_r1 in
      FApi.t_internal
        (FApi.t_seqsub t_conseq
           [FApi.t_try t_trivial; t_bdhoare_skip_r_low])
        tc

  let t_bdhoare_skip = FApi.t_low0 "bdhoare-skip" t_bdhoare_skip_r

  (* ------------------------------------------------------------------ *)
  let t_equiv_skip_r tc =
    let es = tc1_as_equivS tc in

    if not (List.is_empty es.es_sl.s_node) then
      tc_error !!tc ~who:"skip" "left instruction list is not empty";
    if not (List.is_empty es.es_sr.s_node) then
      tc_error !!tc ~who:"skip" "right instruction list is not empty";

    let concl = map_ts_inv2 f_imp (es_pr es) (es_po es) in
    let concl = EcSubst.f_forall_mems_ts_inv es.es_ml es.es_mr concl in
    FApi.xmutate1 tc `Skip [concl]

  let t_equiv_skip = FApi.t_low0 "equiv-skip" t_equiv_skip_r
end

(* -------------------------------------------------------------------- *)
let t_skip =
  t_hS_or_bhS_or_eS
    ~th: LowInternal.t_hoare_skip
    ~teh: LowInternal.t_ehoare_skip
    ~tbh:LowInternal.t_bdhoare_skip
    ~te: LowInternal.t_equiv_skip
