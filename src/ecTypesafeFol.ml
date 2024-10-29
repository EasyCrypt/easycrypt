open EcUtils
open EcAst
open EcTypes
open EcCoreFol
open EcUnify
open EcSubst
open EcEnv

module Map = Batteries.Map

module BI = EcBigInt
module Mp = EcPath.Mp
module Sp = EcPath.Sp
module Sm = EcPath.Sm
module Sx = EcPath.Sx
module UE = EcUnify.UniEnv

type form     = EcAst.form
type f_node   = EcAst.f_node
type ty       = EcTypes.ty

let (%) f g = fun x -> f (g x)

exception InsufficientArguments

let tfrom_tlist ty =
  let p_list = EcCoreLib.CI_List.p_list in
  match ty.ty_node with
  | Tconstr (p, [ty]) when p = p_list -> ty
  | _ -> assert false

let tfrom_tfun2 ty =
  match ty.ty_node with
  | Tfun (a, b) -> (a, b)
  | _ -> assert false

let unroll_ftype (ty:ty) : ty list * ty =
  let rec doit (tys: ty list) (ty: ty) : ty list * ty =
    match ty.ty_node with
    | Tfun _ -> let t1, t2 = tfrom_tfun2 ty in doit (t1::tys) t2
    | _ -> (List.rev tys, ty) 
  in

  doit [] ty

let ty_var_from_ty (ty:ty) : ty list =
  match ty.ty_node with
  | Tconstr (_, args) -> args
  | _ -> assert false (* FIXME: how to handle this case ? *)

(* Returned list is (tyvar, ty) *)
let rec match_ty_tyargs (ty: ty) (tyargs: ty) : (ty * ty) list = 
  match (ty.ty_node, tyargs.ty_node) with
  | (Tconstr (p1, args1), Tconstr (p2, args2)) when p1 = p2 && (List.compare_lengths args1 args2 = 0) ->
    List.flatten @@ List.map2 match_ty_tyargs args1 args2
  | (Ttuple args1, Ttuple args2) when (List.compare_lengths args1 args2 = 0) -> 
    List.flatten @@ List.map2 match_ty_tyargs args1 args2
  | (Tfun (ty11, ty12), Tfun (ty21, ty22)) ->
    (match_ty_tyargs ty11 ty21) @ (match_ty_tyargs ty12 ty22)
  | (_, Tvar _) -> [(ty, tyargs)]
  | (_, Tunivar _) -> [(ty, tyargs)]
  | _ -> assert false

let rec sub_ty_tyargs (vals: (ty, ty) Map.t) (ty: ty) : ty =
  match ty.ty_node with
  | (Tconstr (p1, args1)) -> tconstr p1 (List.map (sub_ty_tyargs vals) args1)
  | (Ttuple args1) -> ttuple (List.map (sub_ty_tyargs vals) args1)
  | (Tfun (ty_arg, ty_ret)) -> tfun (sub_ty_tyargs vals ty_arg) (sub_ty_tyargs vals ty_ret)
  | (Tvar _) -> Map.find ty vals
  | (Tunivar _) -> Map.find ty vals
  | (Tglob _) -> assert false


let open_oper_ue op ue =
  (* Maybe list map works fine because ue is imperative? *)
  let open EcDecl in
  let ue, tys = List.fold_left_map (fun ue _ -> (ue, EcUnify.UniEnv.fresh ue)) ue op.op_tparams in
  (tys, open_oper op tys)

let f_app_safe ?(full=true) (env: env) (f: EcPath.path) (args: form list) =
  let ue = UE.create None in
  let p_f, o_f = EcEnv.Op.lookup (EcPath.toqsymbol f) env in
  let tvars,(newt,f_kind) = open_oper_ue o_f ue in
  let rty = UE.fresh ue in
  let fty = toarrow (List.map (fun f -> f.f_ty) args) rty in
  let () = begin
  try
  (EcUnify.unify env ue fty newt)
  with 
  | UnificationFailure (`TcCtt (ty, sp)) -> raise (UnificationFailure (`TcCtt (ty, sp)))
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
  | Tfun _ -> raise InsufficientArguments
  | _ -> f_app op args rty
  else
  f_app op args rty
  
let rec fapply_safe ?(redmode = EcReduction.full_red) (hyps: LDecl.hyps) (f: form) (fs: form list) : form =
  match f.f_node with
  | Fop (pth, _) -> 
    f_app_safe (LDecl.toenv hyps) pth fs |> EcCallbyValue.norm_cbv redmode hyps
  | Fapp (fop, args) -> 
    (* let new_args = args @ fs in *)
    (* let pp_form = EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps)) in *)
    (* let pp_forms fmt = List.iter (Format.fprintf fmt "%a, " pp_form) in *)
    (* Format.eprintf "new_args: %a@." pp_forms new_args; *)
    fapply_safe ~redmode hyps fop (args @ fs)
  | Fquant (Llambda, binds, f) ->
    assert (List.compare_lengths binds fs >= 0);
    let subst = 
      List.fold_left2  
      (fun subst b f -> EcSubst.add_flocal subst (fst b) f) EcSubst.empty binds fs
    in
    let binds = List.drop (List.length fs) binds in
    let f = f_quant Llambda binds (EcSubst.subst_form subst f) in
    EcCallbyValue.norm_cbv redmode hyps f
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
  | _ -> assert false
