(* -------------------------------------------------------------------- *)
open EcUtils
open EcModules
open EcFol

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

    let concl = f_imp hs.hs_pr hs.hs_po in
    let concl = f_forall_mems [hs.hs_m] concl in

    FApi.xmutate1 tc `Skip [concl]

  let t_hoare_skip = FApi.t_low0 "hoare-skip" t_hoare_skip_r

  let t_choare_skip_r tc =
    let chs = tc1_as_choareS tc in

    if not (List.is_empty chs.chs_s.s_node) then
      tc_error !!tc "instruction list is not empty";

    let cost_cond =
      f_xle f_x0 (EcCHoare.cost_flatten chs.chs_co) in
    let post = f_and chs.chs_po cost_cond in
    let concl = f_imp chs.chs_pr post in
    let concl = f_forall_mems [chs.chs_m] concl in

    FApi.xmutate1 tc `Skip [concl]

  let t_choare_skip = FApi.t_low0 "choare-skip" t_choare_skip_r

  (* ------------------------------------------------------------------ *)
  let t_bdhoare_skip_r_low tc =
    let bhs = tc1_as_bdhoareS tc in

    if not (List.is_empty bhs.bhs_s.s_node) then
      tc_error !!tc ~who:"skip" "instruction list is not empty";
    if bhs.bhs_cmp <> FHeq && bhs.bhs_cmp <> FHge then
      tc_error !!tc ~who:"skip" "";

    let concl = f_imp bhs.bhs_pr bhs.bhs_po in
    let concl = f_forall_mems [bhs.bhs_m] concl in
    let goals =
      if   f_equal bhs.bhs_bd f_r1
      then [concl]
      else [f_eq bhs.bhs_bd f_r1; concl]
    in

    FApi.xmutate1 tc `Skip goals

  (* ------------------------------------------------------------------ *)
  let t_bdhoare_skip_r tc =
    let t_trivial = FApi.t_seqs [t_simplify ~delta:`No; t_split; t_fail] in
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

    let concl = f_imp es.es_pr es.es_po in
    let concl = f_forall_mems [es.es_ml; es.es_mr] concl in
    FApi.xmutate1 tc `Skip [concl]

  let t_equiv_skip = FApi.t_low0 "equiv-skip" t_equiv_skip_r
end

(* -------------------------------------------------------------------- *)
let t_skip =
  t_hS_or_chS_or_bhS_or_eS
    ~th: LowInternal.t_hoare_skip
    ~tch:LowInternal.t_choare_skip
    ~tbh:LowInternal.t_bdhoare_skip
    ~te: LowInternal.t_equiv_skip
