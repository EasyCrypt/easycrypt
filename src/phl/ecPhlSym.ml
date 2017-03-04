(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(*-------------------------------------------------------------------- *)
open EcFol
open EcCoreGoal
open EcLowPhlGoal

(*-------------------------------------------------------------------- *)
let build_sym ml mr pr po =
  let s = Fsubst.f_subst_id in
  let s = Fsubst.f_bind_mem s ml mr in
  let s = Fsubst.f_bind_mem s mr ml in
  let s = Fsubst.f_subst s in
  (s pr, s po)

(*-------------------------------------------------------------------- *)
let t_equivF_sym tc =
  let ef    = tc1_as_equivF tc in
  let pr,po = build_sym mleft mright ef.ef_pr ef.ef_po in
  let cond  = f_equivF pr ef.ef_fr ef.ef_fl po in
  FApi.xmutate1 tc `EquivSym [cond]

(*-------------------------------------------------------------------- *)
let t_equivS_sym tc =
  let es    = tc1_as_equivS tc in
  let pr,po = build_sym (fst es.es_ml) (fst es.es_mr) es.es_pr es.es_po in
  let cond  = f_equivS_r {
    es_ml = fst es.es_ml, snd es.es_mr;
    es_mr = fst es.es_mr, snd es.es_ml;
    es_sl = es.es_sr;
    es_sr = es.es_sl;
    es_pr = pr;
    es_po = po; } in

  FApi.xmutate1 tc `EquivSym [cond]

(*-------------------------------------------------------------------- *)
let t_equiv_sym tc =
  match (FApi.tc1_goal tc).f_node with
  | FequivF _ -> t_equivF_sym tc
  | FequivS _ -> t_equivS_sym tc
  | _ -> tc_error_noXhl ~kinds:[`Equiv `Any] !!tc
