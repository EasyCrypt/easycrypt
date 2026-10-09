(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcAst
open EcTypes
open EcFol
open EcModules
open EcEnv
open EcPV

open EcCoreGoal

(* -------------------------------------------------------------------- *)
let check_concrete (pf : proofenv) (env : env) (f : xpath) =
  if NormMp.is_abstract_fun f env then
    tc_error_lazy pf (fun fmt ->
      let ppe = EcPrinting.PPEnv.ofenv env in
      Format.fprintf fmt
        "The function %a is abstract. Provide an invariant to the [proc] tactic"
        (EcPrinting.pp_funname ppe) f)

let ensure_concrete (name : string) (env : env) (f : xpath) =
  if NormMp.is_abstract_fun f env then
    failwith (name ^ ": the procedure is abstract")

(* -------------------------------------------------------------------- *)
let subst_pre (env : env) (fs : funsig) (m : memory) (s : PVM.subst) =
  let fresh ov =
    match ov.ov_name with
    | None   -> assert false;
    | Some v -> { v_name = v; v_type = ov.ov_type }
  in
  let v = List.map (fun v -> f_pvloc (fresh v) m) fs.fs_anames in
  PVM.add env pv_arg m (map_ss_inv ~m f_tuple v).inv s

(* -------------------------------------------------------------------- *)
(* FIXME: oracles should ensure they preserve the state of the adversaries
 *
 * Two solutions:
 *   - add the equalities in the pre and post.
 *   - ensure that oracle doesn't write the adversaries states
 *
 * See [ospec] in [EcEquivFunAbs] / [EcEquivFunAbsUpto]. *)
let check_oracle_use (env : env) (adv : mpath) (o : xpath) =
  let restr = { mr_empty with ur_neg = Sx.empty, Sm.singleton adv } in

  (* This only checks the memory restrictions. *)
  EcTyping.check_mem_restr_fun env o restr

(* -------------------------------------------------------------------- *)
let lossless_hyps (env : env) (top : mpath) (sub : EcSymbols.symbol) =
  let clear_to_top = { mr_empty with ur_neg = Sx.empty, Sm.singleton top } in

  let sig_ = EcEnv.NormMp.sig_of_mp env top in
  let bd =
    List.map
      (fun (id, mt) ->
         (id, GTmodty (mt, clear_to_top))
      ) sig_.mis_params
  in
  (* WARN: this implies that the oracle do not have access to top *)
  let args  = List.map (fun (id,_) -> EcPath.mident id) sig_.mis_params in
  let concl = f_losslessF (EcPath.xpath (EcPath.m_apply top args) sub) in
  let calls =
    let name = sub in
    (EcSymbols.Msym.find name sig_.mis_oinfos) |> OI.allowed
  in
  let hyps = List.map f_losslessF calls in
    f_forall bd (f_imps hyps concl)

(* -------------------------------------------------------------------- *)
let to_code (env : env) (f : xpath) (m : memory) =
  let fd = Fun.by_xpath f env in
  let me = EcMemory.empty_local ~witharg:false m in

  let args =
    let freshen_arg i ov =
      match ov.ov_name with
      | None   -> { ov with ov_name = Some (Printf.sprintf "arg%d" (i + 1)) }
      | Some _ -> ov
    in List.mapi freshen_arg fd.f_sig.fs_anames
  in

  let (me, args) = EcMemory.bindall_fresh args me in

  let res = { ov_name = Some "r"; ov_type = fd.f_sig.fs_ret; } in

  let me, res = EcMemory.bind_fresh res me in

  let eargs = List.map (fun v -> e_var (pv_loc (oget v.ov_name)) v.ov_type) args in
  let args =
    let var ov = { v_name = oget ov.ov_name; v_type = ov.ov_type } in
    List.map var args
  in

  let icall =
    i_call (Some (LvVar (pv_loc (oget res.ov_name), res.ov_type)), f, eargs)
  in (me, stmt [icall], res, args)

let add_var env vfrom mfrom v m s =
  PVM.add env vfrom mfrom (f_pvar (pv_loc (oget v.ov_name)) v.ov_type m).inv s

let add_var_tuple env vfrom mfrom vs m s =
  let vs =
    List.map (fun v -> f_pvar (pv_loc v.v_name) v.v_type m) vs
  in PVM.add env vfrom mfrom (map_ss_inv ~m f_tuple vs).inv s
