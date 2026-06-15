open EcUtils
open EcAst
open EcTypes
open EcCoreFol
open EcUnify
open EcSubst
open EcEnv

module UE = EcUnify.UniEnv

type form = EcAst.form

let open_oper_ue op ue =
  (* Maybe list map works fine because ue is imperative? *)
  let open EcDecl in
  let _ue, tys = List.fold_left_map (fun ue _ -> (ue, EcUnify.UniEnv.fresh ue)) ue op.op_tparams in
  (tys, open_oper op tys)

let f_app_safe (env: env) (f: EcPath.path) (args: form list) =
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
  f_app op args rty
  
let fapply_safe
    ?(redmode = EcReduction.full_red) (hyps: LDecl.hyps)
    (f: form) (fs: form list) : form =
  let env = LDecl.toenv hyps in
  (* type of [f] applied to its first [n] arguments *)
  let rec result_ty (n : int) (ty : ty) : ty =
    if n <= 0 then ty
    else match (ty_hnorm ty env).ty_node with
      | Tfun (_, codom) -> result_ty (n - 1) codom
      | _ -> ty
  in
  let rty = result_ty (List.length fs) f.f_ty in
  f_app f fs rty |> EcCallbyValue.norm_cbv redmode hyps
