(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcEnv
open EcPV

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module PT  = EcProofTerm
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let t_core_phoare_deno pre post tc =
  let env, _, concl = FApi.tc1_eflat tc in

  let cmp, f, bd, concl_post =
    match concl.f_node with
    | Fapp ({f_node = Fop (op, _)}, [f; bd])
        when is_pr f && EcPath.p_equal op EcCoreLib.p_real_le ->
      (FHle, f, bd, fun ev -> f_imp_simpl ev post)

    | Fapp ({f_node = Fop (op, _)}, [f; bd])
        when is_pr f && EcPath.p_equal op EcCoreLib.p_eq ->
      (FHeq, f, bd, f_iff_simpl post)

    | Fapp ({f_node = Fop (op, _)}, [bd; f])
        when is_pr f && EcPath.p_equal op EcCoreLib.p_real_le ->
      (FHge, f, bd, f_imp_simpl post)

    | _ -> tc_error !!tc "invalid goal shape"
  in

  let (m, f, args, ev) = destr_pr f in
  let concl_e = f_bdHoareF pre f post cmp bd in
  let fun_ = EcEnv.Fun.by_xpath f env in

  (* building the substitution for the pre *)
  let sargs = PVM.add env (pv_arg f) mhr args PVM.empty in
  let smem = Fsubst.f_bind_mem Fsubst.f_subst_id mhr m in
  let concl_pr = Fsubst.f_subst smem (PVM.subst env sargs pre) in

  (* building the substitution for the post *)
  (* FIXME:
   * let smem_ = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mhr in
   * let ev   = Fsubst.f_subst smem_ ev in *)
  let me = EcEnv.Fun.actmem_post mhr f fun_ in
  let concl_po = f_forall_mems [me] (concl_post ev) in

  FApi.xmutate1 tc `HlDeno [concl_e; concl_pr; concl_po]

(* -------------------------------------------------------------------- *)
let t_phoare_deno_r pre post tc =
  let concl = FApi.tc1_goal tc in

  match concl.f_node with
  | Fapp ({f_node = Fop (op, _)}, [bd; f])
      when EcPath.p_equal op EcCoreLib.p_real_ge ->
    FApi.t_seq
      (t_apply_s EcCoreLib.p_rle_ge_sym [] ~args:[f; bd] ~sk:1)
      (t_core_phoare_deno pre post)
      tc

  | Fapp ({f_node = Fop (op, _)}, [f; _bd])
      when EcPath.p_equal op EcCoreLib.p_eq && not (is_pr f) ->
    FApi.t_seq t_symmetry (t_core_phoare_deno pre post) tc

  | _ -> t_core_phoare_deno pre post tc

(* -------------------------------------------------------------------- *)
let t_equiv_deno_r pre post tc =
  let env, _, concl = FApi.tc1_eflat tc in

  let cmp, f1, f2 =
    match concl.f_node with
    | Fapp({f_node = Fop(op,_)}, [f1;f2]) when is_pr f1 && is_pr f2 &&
        (EcPath.p_equal op EcCoreLib.p_eq ||
           EcPath.p_equal op EcCoreLib.p_real_le ||
           EcPath.p_equal op EcCoreLib.p_real_ge) ->
      let cmp =
        if EcPath.p_equal op EcCoreLib.p_eq then `Eq
        else if EcPath.p_equal op EcCoreLib.p_real_le then `Le else `Ge in
      cmp, f1, f2

    | _ -> tc_error !!tc "invalid goal shape"

 in

  let (ml,fl,argsl,evl) = destr_pr f1 in
  let (mr,fr,argsr,evr) = destr_pr f2 in
  let concl_e = f_equivF pre fl fr post in
  let funl = EcEnv.Fun.by_xpath fl env in
  let funr = EcEnv.Fun.by_xpath fr env in

  (* building the substitution for the pre *)
  (* we substitute param by args and left by ml and right by mr *)
  let sargs = PVM.add env (pv_arg fr) mright argsr PVM.empty in
  let sargs = PVM.add env (pv_arg fl) mleft argsl sargs in
  let smem  = Fsubst.f_subst_id in
  let smem  = Fsubst.f_bind_mem smem mright mr in
  let smem  = Fsubst.f_bind_mem smem mleft  ml in
  let concl_pr = Fsubst.f_subst smem (PVM.subst env sargs pre) in

  (* building the substitution for the post *)
  let smeml = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mleft in
  let smemr = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mright in
  let evl   = Fsubst.f_subst smeml evl in
  let evr   = Fsubst.f_subst smemr evr in
  let cmp   =
    match cmp with
    | `Eq -> f_iff evl evr
    | `Le -> f_imp evl evr
    | `Ge -> f_imp evr evl in

  let mel = EcEnv.Fun.actmem_post mleft fl funl in
  let mer = EcEnv.Fun.actmem_post mright fr funr in
  let concl_po = f_forall_mems [mel;mer] (f_imp post cmp) in

  FApi.xmutate1 tc `HlDeno [concl_e; concl_pr; concl_po]

(* -------------------------------------------------------------------- *)
let t_phoare_deno = FApi.t_low2 "phoare-deno" t_phoare_deno_r
let t_equiv_deno  = FApi.t_low2 "equiv-deno"  t_equiv_deno_r

(* -------------------------------------------------------------------- *)
let process_phoare_deno info tc =
  let error () =
    tc_error !!tc "the conclusion is not a suitable Pr expression" in

  let process_cut (pre, post) =
    let hyps, concl = FApi.tc1_flat tc in
    let cmp, f, bd =
      match concl.f_node with
      | Fapp ({f_node = Fop (op, _)}, [f1; f2])
          when EcPath.p_equal op EcCoreLib.p_eq
        ->
             if is_pr f1 then (FHeq, f1, f2)
        else if is_pr f2 then (FHeq, f2, f1)
        else error ()

      | Fapp({f_node = Fop (op, _)}, [f1; f2])
          when EcPath.p_equal op EcCoreLib.p_real_le
        ->
             if is_pr f1 then (FHle, f1, f2) (* f1 <= f2 *)
        else if is_pr f2 then (FHge, f2, f1) (* f2 >= f1 *)
        else error ()

      | Fapp ({f_node = Fop (op, _)}, [f1; f2])
          when EcPath.p_equal op EcCoreLib.p_real_ge
        ->
             if is_pr f1 then (FHge, f1, f2) (* f1 >= f2 *)
        else if is_pr f2 then (FHle, f2, f1) (* f2 <= f1 *)
        else error ()

      | _ -> error ()
    in

    let _, f, _, event = destr_pr f in
    let penv, qenv = LDecl.hoareF f hyps in
    let pre  = pre  |> omap_dfl (fun p -> TTC.pf_process_formula !!tc penv p) f_true in
    let post = post |> omap_dfl (fun p -> TTC.pf_process_formula !!tc qenv p) event in

    f_bdHoareF pre f post cmp bd
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut
      ~prcut:process_cut tc info in

  let pre, post =
    let bhf = pf_as_bdhoareF !!tc ax in
      (bhf.bhf_pr, bhf.bhf_po)
  in

  FApi.t_first (t_apply pt) (t_phoare_deno pre post tc)

(* -------------------------------------------------------------------- *)
let process_equiv_deno info tc =
  let process_cut (pre, post) =
    let hyps, concl = FApi.tc1_flat tc in

    let _op, f1, f2 =
      match concl.f_node with
      | Fapp ({f_node = Fop (op, _)}, [f1; f2]) when is_pr f1 && is_pr f2 ->
          (op, f1, f2)

      | _ -> tc_error !!tc "invalid goal shape"
    in

    let _,fl,_,_ = destr_pr f1 in
    let _,fr,_,_ = destr_pr f2 in

    let penv, qenv = LDecl.equivF fl fr hyps in
    let pre  = pre  |> omap_dfl (fun p -> TTC.pf_process_formula !!tc penv p) f_true in
    let post = post |> omap_dfl (fun p -> TTC.pf_process_formula !!tc qenv p) f_true in
    f_equivF pre fl fr post
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut
      ~prcut:process_cut tc info in

  let pre, post =
    let ef = pf_as_equivF !!tc ax in
      (ef.ef_pr, ef.ef_po)
  in

  FApi.t_first (t_apply pt) (t_equiv_deno pre post tc)

(* -------------------------------------------------------------------- *)
type denoff = ((pformula option) tuple2) fpattern

let process_deno mode info g =
  match mode with
  | `PHoare -> process_phoare_deno info g
  | `Equiv  -> process_equiv_deno  info g
