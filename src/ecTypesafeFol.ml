open EcUtils
open EcAst
open EcTypes
open EcCoreFol
open EcUnify
open EcSubst
open EcEnv

module UE = EcUnify.UniEnv

type form     = EcAst.form

exception InsufficientArguments

let open_oper_ue op ue =
  (* Maybe list map works fine because ue is imperative? *)
  let open EcDecl in
  let _ue, tys = List.fold_left_map (fun ue _ -> (ue, EcUnify.UniEnv.fresh ue)) ue op.op_tparams in
  (tys, open_oper op tys)

let f_app_safe ?(full=true) (env: env) (f: EcPath.path) (args: form list) =
  let ue = UE.create None in
  let p_f, o_f = EcEnv.Op.lookup (EcPath.toqsymbol f) env in
  let tvars,(newt, _f_kind) = open_oper_ue o_f ue in
  let rty = UE.fresh ue in
  let fty = toarrow (List.map (fun f -> f.f_ty) args) rty in
  let () = begin
  try
  (EcUnify.unify env ue fty newt)
  with 
  | UnificationFailure (`TyUni (ty1, ty2)) -> 
    let pp_type = (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) in
    Format.eprintf "Failed to unify types (%a, %a) in call to %s@." pp_type ty1 pp_type ty2 
    (let h,t = EcPath.toqsymbol f in List.fold_right (fun a b -> a ^ "." ^ b) h t); 
    raise (UnificationFailure (`TyUni (ty1, ty2)))
  end 
  in
  let uidmap = UE.assubst ue in
  let subst = EcCoreSubst.Tuni.subst uidmap in
  let rty = EcCoreSubst.ty_subst subst rty in
  let newt = EcCoreSubst.ty_subst subst newt in
  let tvars = List.map (EcCoreSubst.ty_subst subst) tvars in
  let op = f_op p_f tvars newt in
  if full then
  match rty.ty_node with
  | Tfun _ -> Format.eprintf "op: %a@.args: " (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) op; 
    List.iter (fun a -> Format.eprintf "%a, " (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) a) args; Format.eprintf "@.";
    raise InsufficientArguments
  | _ -> f_app op args rty
  else
  f_app op args rty
  
let rec fapply_safe ?(redmode = EcReduction.full_red) (hyps: LDecl.hyps) (f: form) (fs: form list) : form =
(*
  Format.eprintf "Applying forms:@.%a@.To form: %a@."
  (fun fmt fs -> List.iter (fun f -> Format.fprintf fmt "%a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps))) f) fs) fs 
  (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps))) f;
*)
  match f.f_node with
  | Fop (pth, _) -> 
    f_app_safe ~full:false (LDecl.toenv hyps) pth fs |> EcCallbyValue.norm_cbv redmode hyps
  | Fapp (fop, args) -> 
    (* let new_args = args @ fs in *)
    (* let pp_form = EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps)) in *)
    (* let pp_forms fmt = List.iter (Format.fprintf fmt "%a, " pp_form) in *)
    (* Format.eprintf "new_args: %a@." pp_forms new_args; *)
    fapply_safe ~redmode hyps fop (args @ fs)
  | Fquant (Llambda, binds, f) ->
    assert (List.compare_lengths binds fs >= 0);
    let subst_bnds, rem_bnds = List.takedrop (List.length fs) binds in
    let subst = 
      List.fold_left2  
      (fun subst b f -> EcSubst.add_flocal subst (fst b) f) EcSubst.empty subst_bnds fs
    in
    let f = f_quant Llambda rem_bnds (EcSubst.subst_form subst f) in
    EcCallbyValue.norm_cbv redmode hyps f
(* FIXME PR
  | Fquant  (qtf, _, _) -> assert false
  | Fif     (f, ft, ff) -> assert false
  | Fmatch  (f, fs, t) -> assert false
  | Flet    (lpat, f, fb) -> assert false
  | Fint    (i) -> assert false
  | Flocal  (id) -> assert false
  | Fpvar   (pv, m) -> assert false
  | Fglob   (id, m) -> assert false
  | Ftuple  (fs) -> assert false
  | Fproj   (f, i) -> assert false
*)
  | _ -> assert false
