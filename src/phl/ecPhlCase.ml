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
let t_ehoare_case_r ?(simplify = true) f tc =
  let _ = simplify in
  let hs = tc1_as_ehoareS tc in
  let concl1 = f_eHoareS_r { hs with ehs_pr = f_interp_ehoare_form f hs.ehs_pr } in
  let concl2 = f_eHoareS_r { hs with ehs_pr = f_interp_ehoare_form (f_not f) hs.ehs_pr} in
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
  let es = tc1_as_qequivS tc in
  EcQuantum.check_classical ~on:[fst es.es_ml; fst es.es_mr] f tc;
  let pr = es.es_pr in
  let concl1 = f_qequivS_r { es with es_pr = { pr with ec_f = fand pr.ec_f f }} in
  let concl2 = f_qequivS_r { es with es_pr = { pr with ec_f = fand pr.ec_f (f_not f) }} in
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
  t_hS_or_bhS_or_eS
    ~th:(t_hoare_case ?simplify f)
    ~teh:(t_ehoare_case ?simplify f)
    ~tbh:(t_bdhoare_case ?simplify f)
    ~te:(t_equiv_case ?simplify f)
    tc

(* -------------------------------------------------------------------- *)
let t_hl_case ?simplify = FApi.t_low1 "hl-case" (t_hl_case_r ?simplify)
