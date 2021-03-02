(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
open EcFol
open EcCoreGoal
open EcLowPhlGoal

(* --------------------------------------------------------------------- *)
let t_hoare_case_r ?(simplify = true) f tc =
  let fand = if simplify then f_and_simpl else f_and in
  let hs = tc1_as_hoareS tc in
  let concl1 = f_hoareS_r { hs with hs_pr = fand hs.hs_pr f } in
  let concl2 = f_hoareS_r { hs with hs_pr = fand hs.hs_pr (f_not f) } in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_bdhoare_case_r ?(simplify = true) f tc =
  let fand = if simplify then f_and_simpl else f_and in
  let bhs = tc1_as_bdhoareS tc in
  let concl1 = f_bdHoareS_r
    { bhs with bhs_pr = fand bhs.bhs_pr f } in
  let concl2 = f_bdHoareS_r
    { bhs with bhs_pr = fand bhs.bhs_pr (f_not f) } in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_equiv_case_r ?(simplify = true) f tc =
  let fand = if simplify then f_and_simpl else f_and in
  let es = tc1_as_equivS tc in
  let concl1 = f_equivS_r { es with es_pr = fand es.es_pr f } in
  let concl2 = f_equivS_r { es with es_pr = fand es.es_pr (f_not f) } in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_hoare_case ?simplify =
  FApi.t_low1 "hoare-case" (t_hoare_case_r ?simplify)

let t_bdhoare_case ?simplify =
  FApi.t_low1 "bdhoare-case" (t_bdhoare_case_r ?simplify)

let t_equiv_case ?simplify =
  FApi.t_low1 "equiv-case" (t_equiv_case_r ?simplify)

(* --------------------------------------------------------------------- *)
let t_hl_case_r ?simplify f tc =
  t_hS_or_bhS_or_eS
    ~th:(t_hoare_case ?simplify f)
    ~tbh:(t_bdhoare_case ?simplify f)
    ~te:(t_equiv_case ?simplify f)
    tc

(* -------------------------------------------------------------------- *)
let t_hl_case ?simplify = FApi.t_low1 "hl-case" (t_hl_case_r ?simplify)
